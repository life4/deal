# built-in
from typing import Tuple, Type

# app
from .._exceptions import ContractError, RaisesContractError
from .._types import ExceptionType
from .base import Base


class Raises(Base):
    exception: ExceptionType = RaisesContractError

    def __init__(self, *exceptions, message: str = None, exception: ExceptionType = None, debug: bool = False):
        """
        Step 1. Set allowed exceptions list.
        """
        self.exceptions: Tuple[Type[Exception], ...] = exceptions
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
        try:
            return self.function(*args, **kwargs)
        except ContractError:
            raise
        except Exception as exc:
            if not isinstance(exc, self.exceptions):
                raise self.exception from exc
            raise
