from functools import update_wrapper
from types import FunctionType, MethodType
from typing import Callable, Generic, Optional, TypeVar

from ._contracts import Contracts


F = TypeVar('F', bound=Callable)
ATTR = '__deal_contract'


class Inherit(Generic[F]):
    _func: F
    _func_name: str
    _cls: Optional[type] = None
    __call__: F

    def __init__(self, func: F) -> None:
        self._func = func
        self._func_name = func.__name__
        update_wrapper(wrapper=self, wrapped=func)

    @classmethod
    def wrap(cls, target):
        # wrap function
        if not isinstance(target, type):
            return cls(target)

        # wrap class
        for attr in dir(target):
            func = getattr(target, attr)
            if not isinstance(func, FunctionType):
                continue
            wrapped = cls(func)  # type: ignore[arg-type]
            wrapped.__set_name__(target, attr)
            setattr(target, attr, wrapped)
        return target

    def __set_name__(self, owner: type, name: str) -> None:
        self._cls = owner
        self._func_name = name

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
        setattr(self._cls, self._func_name, method)
        return method

    def __call__(self, *args, **kwargs):  # type: ignore[no-redef]
        method = self._patch()
        return method(*args, **kwargs)
