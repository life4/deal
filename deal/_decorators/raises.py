from typing import Tuple, Type

from .._exceptions import ContractError, RaisesContractError
from .._types import ExceptionType
from .base import Base, CallableType


class Raises(Base[CallableType]):
    __slots__ = ['exception', 'function', 'exceptions']

    @classmethod
    def _default_exception(cls) -> ExceptionType:
        return RaisesContractError

    def __init__(
        self,
        *exceptions: Type[Exception],
        message: str = None,
        exception: ExceptionType = None,
    ):
        """
        Step 1. Set allowed exceptions list.
        """
        self.exceptions: Tuple[Type[Exception], ...] = exceptions
        super().__init__(
            validator=None,
            message=message,
            exception=exception,
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
