from asyncio import iscoroutinefunction
from functools import update_wrapper
from inspect import isgeneratorfunction
from typing import Callable, Type

from .._exceptions import ExampleContractError
from .base import Base, CallableType


class Example(Base[CallableType]):
    __slots__ = ()

    def __init__(self, validator: Callable[[], bool]) -> None:
        self.validate = self._validator
        self.raw_validator = validator
        self.message = None
        self.exception = self._default_exception()

    @classmethod
    def _default_exception(cls) -> Type[ExampleContractError]:
        return ExampleContractError

    def _validator(self) -> None:
        if not self.raw_validator():
            exc_type = self._default_exception()
            raise exc_type(validator=self.raw_validator)

    def __call__(self, function: CallableType) -> CallableType:
        self.function = function
        if iscoroutinefunction(function):
            async def wrapped_async(*args, **kwargs):
                return await self.function(*args, **kwargs)
            return update_wrapper(wrapped_async, function)  # type: ignore[return-value]

        if isgeneratorfunction(function):
            def wrapped_gen(*args, **kwargs):
                yield from self.function(*args, **kwargs)
            return update_wrapper(wrapped_gen, function)  # type: ignore[return-value]

        def wrapped_func(*args, **kwargs):
            return self.function(*args, **kwargs)
        return update_wrapper(wrapped_func, function)  # type: ignore[return-value]
