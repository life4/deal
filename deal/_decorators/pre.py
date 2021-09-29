from typing import Type

from .._exceptions import PreContractError
from .base import Base, CallableType


class Pre(Base[CallableType]):
    """
    Check contract (validator) before function processing.
    Validate input arguments.
    """

    @classmethod
    def _default_exception(cls) -> Type[Exception]:
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
