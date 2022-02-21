import inspect
from contextlib import suppress
from functools import lru_cache
from typing import Any, Callable, Dict, Optional, Tuple, Type

import vaa

from .._exceptions import ContractError
from .._types import ExceptionType


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


class Validator:
    __slots__ = (
        'exception',
        'signature',
        'validate',
        'validator',
        'raw_validator',
        'message',
        'function',
    )

    exception: ExceptionType
    signature: Optional[inspect.Signature]
    validate: Any
    validator: Any
    raw_validator: Any
    message: Optional[str]
    function: Any

    def __init__(
        self,
        validator, *,
        message: Optional[str] = None,
        exception: ExceptionType,
    ) -> None:
        self.validate = self._init
        self.raw_validator = validator
        self.message = message
        self.exception = exception
        if message and isinstance(self.exception, type):
            self.exception = self.exception(message)

    @property
    def exception_type(self) -> Type[Exception]:
        if isinstance(self.exception, Exception):
            return type(self.exception)
        return self.exception

    def _make_validator(self) -> Callable:
        """
        If needed, wrap the original raw validator by vaa.
        """
        validator = self.raw_validator
        # implicitly wrap in vaa all external validators
        with suppress(TypeError):
            return vaa.wrap(validator, simple=False)

        # implicitly wrap in vaa.simple only funcs with one `_` argument.
        params = _get_signature(validator).parameters
        if set(params) == {'_'}:
            return vaa.simple(validator, error=self.message)

        return validator

    def _exception(self, *, message: Optional[str] = None, errors=None, params=None) -> Exception:
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
            return exception(
                message=message or '',
                validator=self.validator,
                errors=errors,
                params=params,
                origin=getattr(self, 'function', None),
            )

        # raise boring custom exception
        args = []
        if message:
            args.append(message)
        if errors:
            args.append(errors)
        return exception(*args)

    def init(self) -> None:
        self.validator = self._make_validator()
        if hasattr(self.validator, 'is_valid'):
            self.signature = _get_signature(self.function)
            self.validate = self._vaa_validation
        else:
            self.signature = _get_signature(self.validator)
            self.validate = self._simple_validation

    def _init(self, args, kwargs, exc=None) -> None:
        """
        Called as `validator` when the function is called in the first time.
        Does some costly deferred initializations (involving `inspect`).
        Then sets more appropriate validator as `validator` and calls it.
        """
        self.init()
        self.validate(args, kwargs, exc)

    def _vaa_validation(self, args, kwargs, exc=None) -> None:
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
            raise self._exception(params=params) from exc

        # Flatten single error without field to one simple str message.
        # This is for better readability of simple validators.
        if type(errors) is list:  # pragma: no cover
            if type(errors[0]) is vaa.Error:
                if len(errors) == 1:
                    if errors[0].field is None:
                        errors = errors[0].message

        raise self._exception(errors=errors, params=params) from exc

    def _simple_validation(self, args, kwargs, exc=None) -> None:
        """Validate contract using simple validator.

        Simple validator is a validator that reflects the function signature.
        """
        validation_result = self.validator(*args, **kwargs)
        # is invalid (validator returns error message)
        if type(validation_result) is str:
            params = _args_to_vars(args=args, kwargs=kwargs, signature=self.signature)
            raise self._exception(message=validation_result, params=params) from exc
        # is valid (truely result)
        if validation_result:
            return
        # is invalid (falsy result)
        params = _args_to_vars(args=args, kwargs=kwargs, signature=self.signature)
        raise self._exception(params=params) from exc


class RaisesValidator(Validator):
    __slots__ = ('exceptions', )
    exceptions: Tuple[Type[Exception]]

    def __init__(self, exceptions, exception, message) -> None:
        self.exceptions = exceptions
        self.validator = None
        super().__init__(validator=None, message=message, exception=exception)

    def init(self) -> None:
        self.signature = _get_signature(self.function)
        self.validate = self._validate

    def _init(self, args, kwargs, exc=None) -> None:
        self.init()
        self.validate(args, kwargs, exc=exc)

    def _validate(self, args, kwargs, exc=None) -> None:
        exc_type = type(exc)
        if exc_type in self.exceptions:
            return
        # params = _args_to_vars(args=args, kwargs=kwargs, signature=self.signature)
        raise self._exception() from exc_type


class ReasonValidator(Validator):
    __slots__ = ('event', )
    event: Type[Exception]

    def __init__(self, event, **kwargs) -> None:
        self.event = event
        super().__init__(**kwargs)


class InvariantValidator(Validator):
    def init(self) -> None:
        self.signature = None
        self.validator = self._make_validator()
        if hasattr(self.validator, 'is_valid'):
            self.validate = self._vaa_validation
        else:
            self.validate = self._simple_validation

    def _vaa_validation(self, args, kwargs, exc=None) -> None:
        return super()._vaa_validation((), vars(args[0]), exc=exc)
