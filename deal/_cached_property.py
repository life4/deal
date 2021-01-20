# built-in
from typing import Any, Callable, Generic, Optional, Type, TypeVar, overload


T = TypeVar('T')
S = TypeVar('S')


class cached_property(Generic[T]):  # noqa: N801
    func: Callable[[Any], T]

    def __init__(self, func: Callable[[Any], T]) -> None:
        self.func = func  # type: ignore

    @overload
    def __get__(self, instance: None, owner: Optional[Type[Any]] = ...) -> 'cached_property[T]':
        pass

    @overload
    def __get__(self, instance: S, owner: Optional[Type[Any]] = ...) -> T:
        pass

    def __get__(self, obj, cls):
        value = obj.__dict__[self.func.__name__] = self.func(obj)
        return value
