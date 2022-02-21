from functools import update_wrapper
from typing import TYPE_CHECKING, Callable, Generic, List, Optional, TypeVar

from .._exceptions import NoMatchError, PreContractError
from .._state import state


if TYPE_CHECKING:
    from ._contracts import Contracts


F = TypeVar('F', bound=Callable)
ATTR = '__deal_contract'


class Dispatch(Generic[F]):
    _functions: List[F]
    __call__: F

    def __init__(self) -> None:
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
        contracts: 'Optional[Contracts]'
        old_state = state.debug
        state.debug = True
        try:
            for func in self._functions:
                try:
                    return func(*args, **kwargs)
                except PreContractError as exc:
                    contracts = getattr(func, ATTR, None)
                    if contracts is None:
                        raise
                    if exc.origin is not contracts.func:
                        raise
                    exceptions.append(exc)
        finally:
            state.debug = old_state
        raise NoMatchError(tuple(exceptions))
