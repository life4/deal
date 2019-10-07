# built-in
from functools import partial
from typing import Callable

# app
from ._decorators import Ensure, Invariant, Offline, Post, Pre, Raises, Silent
from ._types import ExceptionType


require = pre = Pre
post = Post
ensure = Ensure
inv = invariant = Invariant
raises = Raises


# makes braces for decorator are optional
def _optional(_contract, _func: Callable = None, *, message: str = None,
              exception: ExceptionType = None, debug: bool = False):
    if _func is not None:
        return _contract()(_func)
    return _contract(message=message, exception=exception, debug=debug)


offline = partial(_optional, Offline)
safe = partial(_optional, Raises)
silent = partial(_optional, Silent)


def chain(*contracts) -> Callable[[Callable], Callable]:
    def wrapped(func):
        for contract in contracts:
            func = contract(func)
        return func
    return wrapped


pure = chain(offline, safe, silent)
