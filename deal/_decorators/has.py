# built-in
import sys
from io import StringIO
import socket
from typing import Callable, FrozenSet, TypeVar, Type

# app
from .._exceptions import MarkerError, OfflineContractError, SilentContractError
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
    exception: ExceptionType = MarkerError
    markers: FrozenSet[str]

    def __init__(self, *markers, message: str = None, exception: ExceptionType = None):
        """
        Step 1. Set allowed markers.
        """
        self.markers = frozenset(markers)
        self.message = message
        if exception:
            self.exception = exception

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

    # known markers

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
    def has_io(self) -> bool:
        if self.has_read:
            return True
        if self.has_write:
            return True
        if self.has_stdout:
            return True
        if self.has_stderr:
            return True
        if self.has_network:
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
        if 'stderr' in self.markers:
            return True
        return False

    @property
    def has_import(self) -> bool:
        return 'import' in self.markers

    @property
    def has_global(self) -> bool:
        if 'global' in self.markers:
            return True
        if 'nonlocal' in self.markers:
            return True
        return False

    @property
    def has_read(self) -> bool:
        if 'io' in self.markers:
            return True
        if 'read' in self.markers:
            return True
        return False

    @property
    def has_write(self) -> bool:
        if 'io' in self.markers:
            return True
        if 'write' in self.markers:
            return True
        return False

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

    def _get_exception(self, default: Type[Exception]) -> ExceptionType:
        if self.exception is MarkerError:
            if self.message is None:
                return default
            return default(self.message)

        if self.message is None:
            return self.exception
        if isinstance(self.exception, Exception):
            return self.exception
        return self.exception(self.message)
