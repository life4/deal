import socket

from .. import exceptions
from ..types import ExceptionType
from .base import Base


class Offline(Base):
    exception: ExceptionType = exceptions.OfflineContractError

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
        true_socket = socket.socket
        socket.socket = self.fake_socket
        try:
            return self.function(*args, **kwargs)
        finally:
            socket.socket = true_socket

    def fake_socket(self, *args, **kwargs):
        raise self.exception
