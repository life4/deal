from typing import Type

from .._exceptions import PostContractError
from .base import Base, CallableType


class Ensure(Base[CallableType]):
    """
    Check both arguments and result (validator) after function processing.
    Validate arguments and output result.
    """

    @classmethod
    def _default_exception(cls) -> Type[PostContractError]:
        return PostContractError

    def patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        result = self.function(*args, **kwargs)
        self.validate(*args, result=result, **kwargs)
        return result

    async def async_patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        result = await self.function(*args, **kwargs)
        self.validate(*args, result=result, **kwargs)
        return result

    def patched_generator(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        for result in self.function(*args, **kwargs):
            self.validate(*args, result=result, **kwargs)
            yield result
