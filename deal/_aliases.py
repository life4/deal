# built-in
from functools import partial
from typing import Callable

# app
from . import _decorators
from ._types import ExceptionType


require = pre = _decorators.Pre
post = _decorators.Post
ensure = _decorators.Ensure
inv = invariant = _decorators.Invariant
raises = _decorators.Raises
reason = _decorators.Reason


# makes braces for decorator are optional
def _optional(_contract, _func: Callable = None, *, message: str = None,
              exception: ExceptionType = None, debug: bool = False):
    if _func is not None:
        return _contract()(_func)
    return _contract(message=message, exception=exception, debug=debug)


offline = partial(_optional, _decorators.Offline)
safe = partial(_optional, _decorators.Raises)
silent = partial(_optional, _decorators.Silent)


def chain(*contracts) -> Callable[[Callable], Callable]:
    def wrapped(func):
        for contract in contracts:
            func = contract(func)
        return func
    return wrapped


pure = chain(offline, safe, silent)
