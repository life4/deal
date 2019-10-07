from .. import exceptions
from ..types import ExceptionType
from .base import Base


class Pre(Base):
    """
    Check contract (validator) before function processing.
    Validate input arguments.
    """
    exception: ExceptionType = exceptions.PreContractError

    def patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        self.validate(*args, **kwargs)
        return self.function(*args, **kwargs)
