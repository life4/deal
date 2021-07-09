from typing import Callable, TypeVar

from .._exceptions import PreContractError
from .._types import ExceptionType
from .base import Base


_CallableType = TypeVar('_CallableType', bound=Callable)


class Pre(Base[_CallableType]):
    """
    Check contract (validator) before function processing.
    Validate input arguments.
    """
    __slots__ = ['validator', 'validate', 'exception', 'function']

    @classmethod
    def _default_exception(cls) -> ExceptionType:
        return PreContractError

    def patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        self.validate(*args, **kwargs)
        return self.function(*args, **kwargs)

    async def async_patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        self.validate(*args, **kwargs)
        return await self.function(*args, **kwargs)

    def patched_generator(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        self.validate(*args, **kwargs)
        yield from self.function(*args, **kwargs)
