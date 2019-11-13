# app
from .._exceptions import PostContractError
from .._types import ExceptionType
from .base import Base


class Ensure(Base):
    """
    Check both arguments and result (validator) after function processing.
    Validate arguments and output result.
    """
    exception: ExceptionType = PostContractError

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
