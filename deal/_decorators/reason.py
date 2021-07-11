from typing import Iterator, Type

from .._cached_property import cached_property
from .._exceptions import ReasonContractError
from .._types import ExceptionType
from .base import Base, CallableType, SLOTS


class Reason(Base[CallableType]):
    __slots__ = SLOTS + ['event']

    @classmethod
    def _default_exception(cls) -> ExceptionType:
        return ReasonContractError

    def __init__(self, event: Type[Exception], *args, **kwargs):
        """
        Step 1. Set allowed exceptions list.
        """
        self.event = event
        super().__init__(*args, **kwargs)

    @cached_property
    def exception_type(self) -> Type[Exception]:
        if isinstance(self.exception, Exception):
            return type(self.exception)
        return self.exception

    def patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        try:
            return self.function(*args, **kwargs)
        except self.event as origin:
            try:
                self.validate(*args, **kwargs)
            except self.exception_type:
                raise self.exception from origin
            raise

    async def async_patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        try:
            return await self.function(*args, **kwargs)
        except self.event as origin:
            try:
                self.validate(*args, **kwargs)
            except self.exception_type:
                raise self.exception from origin
            raise

    def patched_generator(self, *args, **kwargs) -> Iterator:
        """
        Step 3. Wrapped function calling.
        """
        try:
            yield from self.function(*args, **kwargs)
        except self.event as origin:
            try:
                self.validate(*args, **kwargs)
            except self.exception_type:
                raise self.exception from origin
            raise
