from typing import Tuple, Type

from .._exceptions import ContractError, RaisesContractError
from .._types import ExceptionType
from .base import Base, CallableType, Defaults
from .validator import Validator


class Raises(Base[CallableType]):
    __slots__ = ('exceptions',)
    exceptions: Tuple[Type[Exception], ...]

    def __init__(
        self,
        *exceptions: Type[Exception],
        message: str = None,
        exception: ExceptionType = None,
    ):
        """
        Step 1. Set allowed exceptions list.
        """
        self.exceptions = exceptions
        super().__init__(
            validator=None,
            message=message,
            exception=exception,
        )

    @staticmethod
    def _defaults() -> Defaults:
        return Defaults(
            exception_type=RaisesContractError,
            validator_type=Validator,
        )

    def patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        try:
            return self.function(*args, **kwargs)
        except ContractError:
            raise
        except Exception as exc:
            if not isinstance(exc, self.exceptions):
                raise self.exception from exc
            raise

    async def async_patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        try:
            return await self.function(*args, **kwargs)
        except ContractError:
            raise
        except Exception as exc:
            if not isinstance(exc, self.exceptions):
                raise self.exception from exc
            raise

    def patched_generator(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        try:
            yield from self.function(*args, **kwargs)
        except ContractError:
            raise
        except Exception as exc:
            if not isinstance(exc, self.exceptions):
                raise self.exception from exc
            raise
