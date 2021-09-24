from .._exceptions import PostContractError
from .._types import ExceptionType
from .base import SLOTS, Base, CallableType


class Ensure(Base[CallableType]):
    """
    Check both arguments and result (validator) after function processing.
    Validate arguments and output result.
    """
    __slots__ = SLOTS

    @classmethod
    def _default_exception(cls) -> ExceptionType:
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
