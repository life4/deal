from functools import update_wrapper
from types import MethodType
from typing import Generic, Optional, TypeVar, Callable
from ._contracts import Contracts


F = TypeVar('F', bound=Callable)
ATTR = '__deal_contract'


class Inherit(Generic[F]):
    _func: F
    _cls: Optional[type] = None
    __call__: F

    def __init__(self, func: F) -> None:
        self._func = func
        update_wrapper(wrapper=self, wrapped=func)

    def __set_name__(self, owner: type, name: str) -> None:
        self._cls = owner

    def _patch(self) -> Callable:
        if self._cls is None:
            return self._func

        patched = self._func
        contracts: Optional[Contracts]
        for base in self._cls.mro()[1:]:
            other = getattr(base, self._func.__name__, None)
            if other is None:
                continue
            contracts = getattr(other, ATTR, None)
            if contracts is None:
                continue
            patched = contracts.wrap(patched)

        method = MethodType(patched, self._cls)
        setattr(self._cls, self._func.__name__, method)
        return method

    def __call__(self, *args, **kwargs):  # type: ignore[no-redef]
        method = self._patch()
        return method(*args, **kwargs)
