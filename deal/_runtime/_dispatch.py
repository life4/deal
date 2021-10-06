from functools import update_wrapper
from typing import Callable, Generic, List, TypeVar

from .._exceptions import NoMatchError, PreContractError


F = TypeVar('F', bound=Callable)


class Dispatch(Generic[F]):
    _functions: List[F]
    __call__: F

    def __init__(self):
        self._functions = []

    @classmethod
    def wrap(cls, func: F) -> 'Dispatch[F]':
        self = cls()
        update_wrapper(wrapper=self, wrapped=func)
        return self

    def register(self, function: F) -> F:
        self._functions.append(function)
        return function

    def __call__(self, *args, **kwargs):  # type: ignore[no-redef]
        exceptions = []
        for func in self._functions:
            try:
                return func(*args, **kwargs)
            except PreContractError as exc:
                exceptions.append(exc)
        raise NoMatchError(tuple(exceptions))
