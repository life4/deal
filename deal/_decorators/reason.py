from typing import Iterator, Type

from .._exceptions import ReasonContractError
from .base import Base, CallableType, Defaults
from .validator import Validator


class Reason(Base[CallableType]):
    __slots__ = ('event',)

    def __init__(self, event: Type[Exception], *args, **kwargs):
        """
        Step 1. Set allowed exceptions list.
        """
        self.event = event
        super().__init__(*args, **kwargs)

    @staticmethod
    def _defaults() -> Defaults:
        return Defaults(
            exception_type=ReasonContractError,
            validator_type=Validator,
        )

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
