# built-in
import sys
from io import StringIO

# app
from .._exceptions import SilentContractError
from .._types import ExceptionType
from .offline import Offline


class PatchedStringIO(StringIO):
    def __init__(self, exception: ExceptionType):
        self.exception = exception

    def write(self, *args, **kwargs):
        raise self.exception


class Silent(Offline):
    exception: ExceptionType = SilentContractError

    def patch(self):
        self.true_stdout = sys.stdout
        self.true_stderr = sys.stderr
        sys.stdout = PatchedStringIO(exception=self.exception)
        sys.stderr = PatchedStringIO(exception=self.exception)

    def unpatch(self):
        sys.stdout = self.true_stdout
        sys.stderr = self.true_stderr
