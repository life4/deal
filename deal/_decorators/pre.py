# app
from .._exceptions import PreContractError
from .._types import ExceptionType
from .base import Base


class Pre(Base):
    """
    Check contract (validator) before function processing.
    Validate input arguments.
    """
    exception: ExceptionType = PreContractError

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
