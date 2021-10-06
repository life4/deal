from inspect import isgeneratorfunction
from asyncio import iscoroutinefunction
from functools import update_wrapper
from typing import Callable, Generic, NamedTuple, Optional, Type, TypeVar

from .._exceptions import ContractError
from .._state import state
from .._types import ExceptionType
from .validator import Validator


#: We use this type in many other subclasses of `Base` decorator.
CallableType = TypeVar('CallableType', bound=Callable)


class Defaults(NamedTuple):
    exception_type: Type[ContractError]
    validator_type: Type[Validator]


class Base(Generic[CallableType]):
    """The base class for all deal contracts.
    """
    __slots__ = ('validator',)
    validator: Validator

    def __init__(self, validator, *, message: str = None,
                 exception: ExceptionType = None):
        defaults = self._defaults()
        self.validator = defaults.validator_type(
            validator=validator,
            exception=exception or defaults.exception_type,
            message=message,
        )

    @property
    def exception(self) -> ExceptionType:
        return self.validator.exception

    @property
    def message(self) -> Optional[str]:
        return self.validator.message

    @property
    def function(self) -> CallableType:
        return self.validator.function

    @property
    def exception_type(self) -> Type[Exception]:
        if isinstance(self.exception, Exception):
            return type(self.exception)
        return self.exception

    def validate(self, *args, **kwargs) -> None:
        state.debug = False
        try:
            self.validator.validate(*args, **kwargs)
        finally:
            state.debug = True

    @staticmethod
    def _defaults() -> Defaults:
        return Defaults(
            exception_type=ContractError,
            validator_type=Validator,
        )

    def __call__(self, function: CallableType) -> CallableType:
        """
        Step 2. Return wrapped function.
        """
        self.validator.function = function

        if iscoroutinefunction(function):
            async def wrapped_async(*args, **kwargs):
                if state.debug:
                    return await self.async_patched_function(*args, **kwargs)
                return await function(*args, **kwargs)
            return update_wrapper(wrapped_async, function)  # type: ignore[return-value]

        if isgeneratorfunction(function):
            def wrapped_gen(*args, **kwargs):
                if state.debug:
                    yield from self.patched_generator(*args, **kwargs)
                else:
                    yield from function(*args, **kwargs)
            return update_wrapper(wrapped_gen, function)  # type: ignore[return-value]

        def wrapped_func(*args, **kwargs):
            if state.debug:
                return self.patched_function(*args, **kwargs)
            return function(*args, **kwargs)
        return update_wrapper(wrapped_func, function)  # type: ignore[return-value]

    def patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        raise NotImplementedError

    async def async_patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        raise NotImplementedError

    def patched_generator(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        raise NotImplementedError
