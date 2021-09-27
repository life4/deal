from asyncio import iscoroutinefunction
from functools import update_wrapper
from typing import Callable, Type
from .base import CallableType
from inspect import isgeneratorfunction
from .._exceptions import ExampleContractError
from .base import Base


class Example(Base[CallableType]):
    """
    Check both arguments and result (validator) after function processing.
    Validate arguments and output result.
    """

    def __init__(self, validator: Callable[[], bool]) -> None:
        super().__init__(validator=validator, message=None, exception=None)

    @classmethod
    def _default_exception(cls) -> Type[Exception]:
        return ExampleContractError

    def _init(self, *args, **kwargs) -> None:
        if not self.raw_validator():
            raise ExampleContractError(validator=self.raw_validator)

    def __call__(self, function: CallableType) -> CallableType:
        self.function = function
        if iscoroutinefunction(function):
            async def wrapped_async(*args, **kwargs):
                self  # add self into clousure
                return await function(*args, **kwargs)
            return update_wrapper(wrapped_async, function)  # type: ignore[return-value]

        if isgeneratorfunction(function):
            def wrapped_gen(*args, **kwargs):
                self
                yield from function(*args, **kwargs)
            return update_wrapper(wrapped_gen, function)  # type: ignore[return-value]

        def wrapped_func(*args, **kwargs):
            self
            return function(*args, **kwargs)
        return update_wrapper(wrapped_func, function)  # type: ignore[return-value]
