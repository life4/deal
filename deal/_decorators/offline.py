# built-in
import socket

# app
from .._exceptions import OfflineContractError
from .._types import ExceptionType
from .base import Base


class Offline(Base):
    exception: ExceptionType = OfflineContractError

    def __init__(self, *, message: str = None, exception: ExceptionType = None, debug: bool = False):
        """
        Step 1. Init params.
        """
        super().__init__(
            validator=None,  # type: ignore
            message=message,
            exception=exception,
            debug=debug,
        )

    def patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        self.patch()
        try:
            return self.function(*args, **kwargs)
        finally:
            self.unpatch()

    async def async_patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        self.patch()
        try:
            return await self.function(*args, **kwargs)
        finally:
            self.unpatch()

    def patched_generator(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        generator = self.function(*args, **kwargs)
        while True:
            self.patch()
            try:
                result = next(generator)
            except StopIteration:
                return
            finally:
                self.unpatch()
            yield result

    def patch(self):
        self.true_socket = socket.socket
        socket.socket = self.fake_socket

    def unpatch(self):
        socket.socket = self.true_socket

    def fake_socket(self, *args, **kwargs):
        raise self.exception
