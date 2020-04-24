# app
# built-in
from typing import Callable, TypeVar

from .._exceptions import PostContractError
from .._types import ExceptionType
from .base import Base


_CallableType = TypeVar('_CallableType', bound=Callable)


class Ensure(Base[_CallableType]):
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

    def patched_generator(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        for result in self.function(*args, **kwargs):
            self.validate(*args, result=result, **kwargs)
            yield result
