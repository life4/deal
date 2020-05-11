# built-in
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
    *exceptions,
    message: str = None,
    exception: ExceptionType = None,
    debug: bool = False,
) -> Callable[[_CallableType], _CallableType]:
    cls = _decorators.Raises[_CallableType]
    return cls(*exceptions, message=message, exception=exception, debug=debug)


def has(
    *markers,
    message: str = None,
    exception: ExceptionType = None,
    debug: bool = False,
) -> Callable[[_CallableType], _CallableType]:
    cls = _decorators.Has[_CallableType]
    return cls(*markers, message=message, exception=exception, debug=debug)


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


@overload
def safe(
    *,
    message: str = None,
    exception: ExceptionType = None,
    debug: bool = False,
) -> Callable[[_CallableType], _CallableType]:
    pass  # pragma: no cover


@overload
def safe(_func: _CallableType) -> _CallableType:
    pass  # pragma: no cover


def safe(_func=None, **kwargs):
    if _func is None:
        return raises(**kwargs)
    return raises()(_func)


def chain(*contracts) -> Callable[[_CallableType], _CallableType]:
    def wrapped(func):
        for contract in contracts:
            func = contract(func)
        return func
    return wrapped


def pure(_func: _CallableType) -> _CallableType:
    return chain(has(), safe)(_func)


def offline(_func: Callable = None, **kwargs):
    if _func is None:
        return has('print', **kwargs)
    return has('print')(_func)


def silent(_func: Callable = None, **kwargs):
    if _func is None:
        return has('network', **kwargs)
    return has('network')(_func)
