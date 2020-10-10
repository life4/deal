# built-in
import inspect
from asyncio import iscoroutinefunction
from contextlib import suppress
from functools import update_wrapper
from typing import Any, Callable, Dict, Generic, NoReturn, TypeVar

# external
import vaa

# app
from .._exceptions import ContractError
from .._state import state
from .._types import ExceptionType


#: We use this type in many other subclasses of `Base` decorator.
_CallableType = TypeVar('_CallableType', bound=Callable)


class Base(Generic[_CallableType]):
    exception: ExceptionType = ContractError
    function: _CallableType  # pytype: disable=not-supported-yet

    def __init__(self, validator, *, message: str = None,
                 exception: ExceptionType = None):
        """
        Step 1. Set contract (validator).
        """
        self.validator = self._make_validator(validator, message=message)
        if exception:
            self.exception = exception
        if message:
            self.exception = self.exception(message)    # type: ignore

    @staticmethod
    def _make_validator(validator, message: str = None):
        if validator is None:
            return None
        # implicitly wrap in vaa all external validators
        with suppress(TypeError):
            return vaa.wrap(validator, simple=False)

        # implicitly wrap in vaa.simple only funcs with one `_` argument.
        if inspect.isfunction(validator):
            params = inspect.signature(validator).parameters
            if set(params) == {'_'}:
                return vaa.simple(validator, error=message)

        return validator

    def validate(self, *args, **kwargs) -> None:
        """
        Step 4. Process contract (validator)
        """

        if hasattr(self.validator, 'is_valid'):
            self._vaa_validation(*args, **kwargs)
        else:
            self._simple_validation(*args, **kwargs)

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
        raise exception(errors or message)

    def _args_to_vars(self, *, args, kwargs: Dict[str, Any], function=None) -> Dict[str, Any]:
        """Convert args and kwargs into dict of params based on the given function.

        Function is not passed for `vaa` validators.
        For simple validators the validator is passed as function.
        If no function passed, wrapped function will be used.
        """
        keep_result = True
        if function is None:
            function = getattr(self, 'function', None)
            keep_result = False
        if function is None:
            return kwargs

        params = kwargs.copy()
        # Do not pass argument named `result` into the function.
        # It is a hack for `deal.ensure` with `vaa` validator.
        if not keep_result and 'result' in kwargs:
            kwargs = kwargs.copy()
            del kwargs['result']

        # detect original function
        function = inspect.unwrap(function)
        # assign *args to real names
        params.update(inspect.getcallargs(function, *args, **kwargs))
        return params

    def _vaa_validation(self, *args, **kwargs) -> None:
        """Validate contract using vaa wrapped validator
        """

        # if it is a decorator for a function, convert positional args into named ones.
        params = self._args_to_vars(args=args, kwargs=kwargs)

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

    def _simple_validation(self, *args, **kwargs) -> None:
        """Validate contract using simple validator.

        Simple validator is a validator that reflects the function signature.
        """
        validation_result = self.validator(*args, **kwargs)
        # is invalid (validator returns error message)
        if isinstance(validation_result, str):
            params = self._args_to_vars(args=args, kwargs=kwargs, function=self.validator)
            self._raise(message=validation_result, params=params)
        # is valid (truely result)
        if validation_result:
            return
        # is invalid (falsy result)
        params = self._args_to_vars(args=args, kwargs=kwargs, function=self.validator)
        self._raise(params=params)

    @property
    def enabled(self) -> bool:
        return state.debug

    def __call__(self, function: _CallableType) -> _CallableType:
        """
        Step 2. Return wrapped function.
        """
        self.function = function

        def wrapped(*args, **kwargs):
            if self.enabled:
                return self.patched_function(*args, **kwargs)
            return function(*args, **kwargs)

        async def async_wrapped(*args, **kwargs):
            if self.enabled:
                return await self.async_patched_function(*args, **kwargs)
            return await function(*args, **kwargs)

        def wrapped_generator(*args, **kwargs):
            if self.enabled:
                yield from self.patched_generator(*args, **kwargs)
            else:
                yield from function(*args, **kwargs)

        if iscoroutinefunction(function):
            new_callable = update_wrapper(async_wrapped, function)
        elif inspect.isgeneratorfunction(function):
            new_callable = update_wrapper(wrapped_generator, function)
        else:
            new_callable = update_wrapper(wrapped, function)
        return new_callable  # type: ignore

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
