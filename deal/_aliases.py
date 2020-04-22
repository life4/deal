# built-in
from functools import partial
from typing import Callable, TypeVar, overload

# app
from . import _decorators
from ._types import ExceptionType


_CallableType = TypeVar('_CallableType', bound=Callable)


def pre(
    validator,
    *,
    message: str = None,
    exception: ExceptionType = None,
    debug: bool = False,
) -> Callable[[_CallableType], _CallableType]:
    return _decorators.Pre[_CallableType](
        validator, message=message, exception=exception, debug=debug,
    )


def post(
    validator,
    *,
    message: str = None,
    exception: ExceptionType = None,
    debug: bool = False,
) -> Callable[[_CallableType], _CallableType]:
    return _decorators.Post[_CallableType](
        validator, message=message, exception=exception, debug=debug,
    )


def ensure(
    validator,
    *,
    message: str = None,
    exception: ExceptionType = None,
    debug: bool = False,
) -> Callable[[_CallableType], _CallableType]:
    return _decorators.Ensure[_CallableType](
        validator, message=message, exception=exception, debug=debug,
    )


def raises(
    validator,
    *,
    message: str = None,
    exception: ExceptionType = None,
    debug: bool = False,
) -> Callable[[_CallableType], _CallableType]:
    return _decorators.Raises[_CallableType](
        validator, message=message, exception=exception, debug=debug,
    )


def reason(
    event: Exception,
    validator,
    *,
    message: str = None,
    exception: ExceptionType = None,
    debug: bool = False,
) -> Callable[[_CallableType], _CallableType]:
    return _decorators.Reason[_CallableType](
        event, validator, message=message, exception=exception, debug=debug,
    )


require = pre
inv = invariant = _decorators.Invariant


# makes braces for decorator are optional
def _optional(
    _contract,
    _func: Callable = None,
    *,
    message: str = None,
    exception: ExceptionType = None,
    debug: bool = False,
):
    if _func is not None:
        return _contract()(_func)
    return _contract(message=message, exception=exception, debug=debug)


@overload
def offline(
    *,
    message: str = None,
    exception: ExceptionType = None,
    debug: bool = False,
) -> Callable[[_CallableType], _CallableType]:
    ...


@overload
def offline(_func: _CallableType) -> _CallableType:
    ...


def offline(
    _func=None,
    *,
    message=None,
    exception=None,
    debug=False,
):
    return _optional(
        _decorators.Offline,
        _func,
        message=message,
        exception=exception,
        debug=debug,
    )


@overload
def safe(
    *,
    message: str = None,
    exception: ExceptionType = None,
    debug: bool = False,
) -> Callable[[_CallableType], _CallableType]:
    ...


@overload
def safe(_func: _CallableType) -> _CallableType:
    ...


def safe(
    _func=None,
    *,
    message=None,
    exception=None,
    debug=False,
):
    return _optional(
        _decorators.Raises,
        _func,
        message=message,
        exception=exception,
        debug=debug,
    )


@overload
def silent(
    *,
    message: str = None,
    exception: ExceptionType = None,
    debug: bool = False,
) -> Callable[[_CallableType], _CallableType]:
    ...


@overload
def silent(_func: _CallableType) -> _CallableType:
    ...


def silent(
    _func=None,
    *,
    message=None,
    exception=None,
    debug=False,
):
    return _optional(
        _decorators.Silent,
        _func,
        message=message,
        exception=exception,
        debug=debug,
    )


def chain(*contracts) -> Callable[[_CallableType], _CallableType]:
    def wrapped(func):
        for contract in contracts:
            func = contract(func)
        return func
    return wrapped


def pure(_func: _CallableType) -> _CallableType:
    return chain(offline, safe, silent)(_func)
