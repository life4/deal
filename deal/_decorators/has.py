# built-in
import sys
from io import StringIO
import socket
from typing import Callable, TypeVar, Set, Type

# app
from .._exceptions import OfflineContractError, SilentContractError
from .._types import ExceptionType
from .base import Base


_CallableType = TypeVar('_CallableType', bound=Callable)


class PatchedStringIO(StringIO):
    def __init__(self, exception: ExceptionType):
        self.exception = exception

    def write(self, *args, **kwargs):
        raise self.exception


class PatchedSocket:
    def __init__(self, exception: ExceptionType = None):
        self.exception = exception

    def __call__(self, *args, **kwargs):
        raise self.exception


class Has(Base[_CallableType]):
    exception: ExceptionType = None

    def __init__(self, *markers, message: str = None, exception: ExceptionType = None, debug: bool = False):
        """
        Step 1. Set allowed markers.
        """
        self.markers: Set[str] = set(markers)
        self.message = message
        self.exception = exception
        self.debug = debug

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

    # chacks

    @property
    def has_network(self) -> bool:
        if 'io' in self.markers:
            return True
        if 'network' in self.markers:
            return True
        if 'socket' in self.markers:
            return True
        return False

    @property
    def has_stdout(self) -> bool:
        if 'io' in self.markers:
            return True
        if 'print' in self.markers:
            return True
        if 'stdout' in self.markers:
            return True
        return False

    @property
    def has_stderr(self) -> bool:
        if 'io' in self.markers:
            return True
        if 'print' in self.markers:
            return True
        if 'stderr' in self.markers:
            return True
        return False

    def _get_exception(self, default: Type[Exception]) -> ExceptionType:
        if self.exception is None:
            if self.message is None:
                return default
            return default(self.message)

        if self.message is None:
            return self.exception
        return self.exception(self.message)

    # patching

    def patch(self):
        if not self.has_network:
            self.true_socket = socket.socket
            socket.socket = PatchedSocket(
                exception=self._get_exception(OfflineContractError),
            )
        if not self.has_stdout:
            self.true_stdout = sys.stdout
            sys.stdout = PatchedStringIO(
                exception=self._get_exception(SilentContractError),
            )
        if not self.has_stderr:
            self.true_stderr = sys.stderr
            sys.stderr = PatchedStringIO(
                exception=self._get_exception(SilentContractError),
            )

    def unpatch(self):
        if not self.has_network:
            socket.socket = self.true_socket
        if not self.has_stdout:
            sys.stdout = self.true_stdout
        if not self.has_stderr:
            sys.stderr = self.true_stderr
