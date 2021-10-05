from asyncio import iscoroutinefunction
from functools import update_wrapper
from inspect import isgeneratorfunction
from typing import Callable

from .._exceptions import ExampleContractError
from .base import Base, CallableType, Defaults
from .validator import Validator


class ExampleValidator(Validator):
    def init(self) -> None:
        pass

    def _init(self) -> None:  # type: ignore[override]
        if not self.raw_validator():
            raise ExampleContractError(validator=self.raw_validator)


class Example(Base[CallableType]):
    __slots__ = ()

    def __init__(self, validator: Callable[[], bool]) -> None:
        super().__init__(validator, message=None, exception=None)

    @staticmethod
    def _defaults() -> Defaults:
        return Defaults(
            exception_type=ExampleContractError,
            validator_type=ExampleValidator,
        )

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
