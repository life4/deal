# built-in
import sys
from io import StringIO

# app
from .._exceptions import SilentContractError
from .._types import ExceptionType
from .base import Base


class PatchedStringIO(StringIO):
    def __init__(self, exception: ExceptionType):
        self.exception = exception

    def write(self, *args, **kwargs):
        raise self.exception


class Silent(Base):
    exception: ExceptionType = SilentContractError

    def __init__(self, *, message: str = None, exception: ExceptionType = None, debug: bool = False):
        """
        Step 1. Init params.
        """
        super().__init__(
            validator=None,
            message=message,
            exception=exception,
            debug=debug,
        )

    def patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        true_stdout = sys.stdout
        true_stderr = sys.stderr
        sys.stdout = PatchedStringIO(exception=self.exception)
        sys.stderr = PatchedStringIO(exception=self.exception)
        try:
            return self.function(*args, **kwargs)
        finally:
            sys.stdout = true_stdout
            sys.stderr = true_stderr

    async def async_patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        true_stdout = sys.stdout
        true_stderr = sys.stderr
        sys.stdout = PatchedStringIO(exception=self.exception)
        sys.stderr = PatchedStringIO(exception=self.exception)
        try:
            return await self.function(*args, **kwargs)
        finally:
            sys.stdout = true_stdout
            sys.stderr = true_stderr
