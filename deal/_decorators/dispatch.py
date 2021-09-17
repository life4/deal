from typing import Callable, Tuple

from .._exceptions import NoMatchError, PreContractError


class Dispatch:
    __slots__ = ['functions']

    def __init__(self, functions: Tuple[Callable, ...]):
        self.functions = functions

    def __call__(self, *args, **kwargs):
        exceptions = []
        for func in self.functions:
            try:
                return func(*args, **kwargs)
            except PreContractError as exc:
                exceptions.append(exc)
        raise NoMatchError(tuple(exceptions))
