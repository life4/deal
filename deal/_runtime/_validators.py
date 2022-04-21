from __future__ import annotations

import inspect
from functools import lru_cache
from typing import Any, Callable

import vaa

from .._exceptions import ContractError
from .._types import ExceptionType


@lru_cache(maxsize=16)
def _get_signature(function: Callable) -> inspect.Signature:
    return inspect.signature(function)


def _args_to_vars(
    *,
    args,
    kwargs: dict[str, Any],
    signature: inspect.Signature | None,
    keep_result: bool = True,
) -> dict[str, Any]:
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


class BorgDict(dict):
    def __getattr__(self, name: str):
        if name in self:
            return self[name]
        raise AttributeError(name)


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
    signature: inspect.Signature | None
    validate: Any
    validator: Any
    raw_validator: Any
    message: str | None
    function: Any

    def __init__(
        self,
        validator, *,
        message: str | None = None,
        exception: ExceptionType,
    ) -> None:
        self.validate = self._init
        self.raw_validator = validator
        self.message = message
        self.exception = exception
        self.function = None
        if message and isinstance(self.exception, type):
            self.exception = self.exception(message)

    @property
    def exception_type(self) -> type[Exception]:
        if isinstance(self.exception, Exception):
            return type(self.exception)
        return self.exception

    def _exception(self, *, message: str | None = None, errors=None, params=None) -> Exception:
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

    def _wrap_vaa(self) -> Any | None:
        try:
            return vaa.wrap(self.raw_validator, simple=False)
        except TypeError:
            pass
        if hasattr(self.raw_validator, 'is_valid'):
            return self.raw_validator
        return None

    def init(self) -> None:
        # implicitly wrap in vaa.simple only funcs with one `_` argument.
        self.signature = None
        val_signature = _get_signature(self.raw_validator)
        if set(val_signature.parameters) == {'_'}:
            self.validator = self.raw_validator
            self.validate = self._short_validation
            if self.function is not None:
                self.signature = _get_signature(self.function)
        else:
            vaa_validator = self._wrap_vaa()
            if vaa_validator is None:
                self.validator = self.raw_validator
                self.signature = _get_signature(self.validator)
                self.validate = self._simple_validation
            else:
                self.validator = vaa_validator
                if self.function is not None:
                    self.signature = _get_signature(self.function)
                self.validate = self._vaa_validation

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
        params = _args_to_vars(
            args=args,
            kwargs=kwargs,
            signature=self.signature,
            keep_result=False,
        )

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

    def _short_validation(self, args, kwargs, exc=None) -> None:
        """Validate contract using simple validator.

        Simple validator is a validator that reflects the function signature.
        """
        params = _args_to_vars(
            args=args,
            kwargs=kwargs,
            signature=self.signature,
            keep_result=False,
        )
        validation_result = self.validator(BorgDict(params))
        # is invalid (validator returns error message)
        if type(validation_result) is str:
            raise self._exception(message=validation_result, params=params) from exc
        # is valid (truely result)
        if validation_result:
            return
        # is invalid (falsy result)
        raise self._exception(params=params) from exc


class RaisesValidator(Validator):
    __slots__ = ('exceptions', )
    exceptions: tuple[type[Exception]]

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
        assert exc is not None
        exc_type = type(exc)
        if exc_type in self.exceptions:
            return
        raise self._exception() from exc_type


class ReasonValidator(Validator):
    __slots__ = ('event', )
    event: type[Exception]

    def __init__(self, event, **kwargs) -> None:
        self.event = event
        super().__init__(**kwargs)


class InvariantValidator(Validator):
    def _vaa_validation(self, args, kwargs, exc=None) -> None:
        return super()._vaa_validation((), vars(args[0]), exc=exc)
