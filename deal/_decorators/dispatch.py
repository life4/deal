from functools import update_wrapper
from typing import Generic, List

from .._exceptions import NoMatchError, PreContractError
from .base import CallableType


class Dispatch(Generic[CallableType]):
    _functions: List[CallableType]
    __call__: CallableType

    def __init__(self):
        self._functions = []

    @classmethod
    def wrap(cls, func: CallableType) -> 'Dispatch[CallableType]':
        self = cls()
        update_wrapper(wrapper=self, wrapped=func)
        return self

    def register(self, function: CallableType) -> CallableType:
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
