# app
from .._exceptions import PostContractError
from .._types import ExceptionType
from .base import Base


class Post(Base):
    """
    Check contract (validator) after function processing.
    Validate output result.
    """
    exception: ExceptionType = PostContractError

    def patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        result = self.function(*args, **kwargs)
        self.validate(result)
        return result
