import inspect
from asyncio import iscoroutinefunction
from contextlib import suppress
from functools import lru_cache, update_wrapper
from typing import Any, Callable, Dict, Generic, NoReturn, Optional, TypeVar

import vaa

from .._exceptions import ContractError
from .._state import state
from .._types import ExceptionType


#: We use this type in many other subclasses of `Base` decorator.
CallableType = TypeVar('CallableType', bound=Callable)

SLOTS = [
    'validator',
    'validate',
    'exception',
    'function',
    'signature',
    'raw_validator',
    'message',
]


@lru_cache(maxsize=16)
def _get_signature(function: Callable) -> inspect.Signature:
    return inspect.signature(function)


def _args_to_vars(
    *,
    args,
    kwargs: Dict[str, Any],
    signature: Optional[inspect.Signature],
    keep_result: bool = True,
) -> Dict[str, Any]:
    """Convert args and kwargs into dict of params based on the given function.

    For simple validators the validator is passed as function.
    """
    if signature is None:
        return kwargs

    params = kwargs.copy()
    # Do not pass argument named `result` into the function.
    # It is a hack for `deal.ensure` with `vaa` validator.
    if not keep_result and 'result' in kwargs:
        kwargs = kwargs.copy()
        del kwargs['result']

    # assign *args to real names
    for name, param in signature.parameters.items():
        params[name] = param.default
    params.update(signature.bind(*args, **kwargs).arguments)
    return params


class Base(Generic[CallableType]):
    exception: ExceptionType = ContractError
    function: CallableType
    signature: Optional[inspect.Signature]
    validate: Any
    validator: Any
    raw_validator: Any
    message: Optional[str]

    def __init__(self, validator, *, message: str = None,
                 exception: ExceptionType = None):
        """
        Step 1. Set contract (validator).
        """
        self.validate = self._init
        self.raw_validator = validator
        self.message = message
        if exception:
            self.exception = exception
        else:
            self.exception = self._default_exception()
        if message:
            self.exception = self.exception(message)    # type: ignore

    @classmethod
    def _default_exception(cls) -> ExceptionType:
        """
        Returns default exception for this contract.
        We can't use class-level defaults for it becuase subclasses use __slots__.
        """
        return cls.exception

    def _make_validator(self) -> Callable:
        """
        If needed, wrap the original raw validator by vaa.
        """
        validator = self.raw_validator
        # implicitly wrap in vaa all external validators
        with suppress(TypeError):
            return vaa.wrap(validator, simple=False)

        # implicitly wrap in vaa.simple only funcs with one `_` argument.
        if inspect.isfunction(validator):
            params = inspect.signature(validator).parameters
            if set(params) == {'_'}:
                return vaa.simple(validator, error=self.message)

        return validator

    def _raise(self, *, message: str = None, errors=None, params=None) -> NoReturn:
        exception = self.exception
        if isinstance(exception, Exception):
            if not message and exception.args:
                message = exception.args[0]
            exception = type(exception)

        # if errors provided, use it as error message
        if errors and isinstance(errors, str):
            message = errors
            errors = None

        # raise beautiful ContractError
        if issubclass(exception, ContractError):
            raise exception(
                message=message or '',
                validator=self.validator,
                errors=errors,
                params=params,
            )

        # raise boring custom exception
        args = []
        if message:
            args.append(message)
        if errors:
            args.append(errors)
        raise exception(*args)

    def _init(self, *args, **kwargs):
        """
        Called as `validator` when the function is called in the first time.
        Does some costly deferred initializations (involving `inspect`).
        Then sets more appropriate validator as `validator` and calls it.
        """
        self.validator = self._make_validator()
        if hasattr(self.validator, 'is_valid'):
            self.signature = _get_signature(self.function)
            self.validate = self._vaa_validation
        else:
            self.signature = _get_signature(self.validator)
            self.validate = self._simple_validation
        return self.validate(*args, **kwargs)

    @state.disabled
    def _vaa_validation(self, *args, **kwargs) -> None:
        """Validate contract using vaa wrapped validator.
        """

        # if it is a decorator for a function, convert positional args into named ones.
        if hasattr(self, 'function'):
            params = _args_to_vars(
                args=args,
                kwargs=kwargs,
                signature=self.signature,
                keep_result=False,
            )
        else:
            params = kwargs

        # validate
        validator = self.validator(data=params)
        if validator.is_valid():
            return

        # if no errors returned, raise the default exception
        errors = validator.errors
        if not errors:
            self._raise(params=params)

        # Flatten single error without field to one simple str message.
        # This is for better readability of simple validators.
        if type(errors) is list:  # pragma: no cover
            if type(errors[0]) is vaa.Error:
                if len(errors) == 1:
                    if errors[0].field is None:
                        errors = errors[0].message

        self._raise(errors=errors, params=params)

    @state.disabled
    def _simple_validation(self, *args, **kwargs) -> None:
        """Validate contract using simple validator.

        Simple validator is a validator that reflects the function signature.
        """
        validation_result = self.validator(*args, **kwargs)
        # is invalid (validator returns error message)
        if type(validation_result) is str:
            params = _args_to_vars(args=args, kwargs=kwargs, signature=self.signature)
            self._raise(message=validation_result, params=params)
        # is valid (truely result)
        if validation_result:
            return
        # is invalid (falsy result)
        params = _args_to_vars(args=args, kwargs=kwargs, signature=self.signature)
        self._raise(params=params)

    def __call__(self, function: CallableType) -> CallableType:
        """
        Step 2. Return wrapped function.
        """
        self.function = function

        if iscoroutinefunction(function):
            async def wrapped_async(*args, **kwargs):
                if state.debug:
                    return await self.async_patched_function(*args, **kwargs)
                return await function(*args, **kwargs)
            return update_wrapper(wrapped_async, function)  # type: ignore[return-value]

        if inspect.isgeneratorfunction(function):
            def wrapped_gen(*args, **kwargs):
                if state.debug:
                    yield from self.patched_generator(*args, **kwargs)
                else:
                    yield from function(*args, **kwargs)
            return update_wrapper(wrapped_gen, function)  # type: ignore[return-value]

        def wrapped_func(*args, **kwargs):
            if state.debug:
                return self.patched_function(*args, **kwargs)
            return function(*args, **kwargs)
        return update_wrapper(wrapped_func, function)  # type: ignore[return-value]

    def patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        raise NotImplementedError

    async def async_patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        raise NotImplementedError

    def patched_generator(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        raise NotImplementedError
