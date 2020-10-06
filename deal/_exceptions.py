import sys
from io import StringIO
from pathlib import Path

from uncompyle6 import deparse_code2str
import pygments
from pygments.formatters.terminal import TerminalFormatter
from pygments.lexers.python import PythonLexer

from ._cached_property import cached_property

root = str(Path(__file__).parent)


def exception_hook(etype, value, tb):
    """Exception hook to remove deal from the traceback for ContractError.
    """
    if not issubclass(etype, ContractError):
        return _excepthook(etype, value, tb)

    # try to reduce traceback by removing `deal` part
    prev_tb = patched_tb = tb
    while patched_tb:
        path: str = patched_tb.tb_frame.f_code.co_filename
        if path.startswith(root):
            prev_tb.tb_next = None
            break
        prev_tb = patched_tb
        patched_tb = patched_tb.tb_next
    else:
        # cannot find deal in the trace, leave it as is
        patched_tb = tb

    return _excepthook(etype, value, patched_tb)


_excepthook = sys.excepthook
sys.excepthook = exception_hook


class ContractError(AssertionError):
    def __init__(self, message: str = '', errors=None, validator=None) -> None:
        self.message = message
        self.errors = errors
        self.validator = validator

        args = []
        if message:
            args.append(message)
        if errors:
            args.append(errors)
        super().__init__(*args)

    @cached_property
    def source(self) -> str:
        if self.validator is None:
            return ''

        if hasattr(self.validator, '__code__'):
            devnull = StringIO()
            source = deparse_code2str(code=self.validator.__code__, out=devnull)
            lines = source.strip('\n').split('\n')
            if len(lines) == 1:
                source = lines[0]
                if source.startswith('return '):
                    source = source[7:]
                return source

        if hasattr(self.validator, '__qualname__'):
            return self.validator.__qualname__
        return repr(self.validator)

    @cached_property
    def colored_source(self) -> str:
        if not self.source:
            return self.source
        source = pygments.highlight(
            code=self.source,
            lexer=PythonLexer(),
            formatter=TerminalFormatter(),
        )
        source = source.rstrip()
        if '\033' not in source:
            source = '\033[94m' + source + '\033[0m'
        return source

    def __str__(self) -> str:
        result = self.message
        if not result and self.errors:
            result = repr(self.errors)
        if not result and self.colored_source:
            result = self.colored_source
        return result


class PreContractError(ContractError):
    pass


class PostContractError(ContractError):
    pass


class InvContractError(ContractError):
    pass


class RaisesContractError(ContractError):
    pass


class ReasonContractError(ContractError):
    pass


class MarkerError(ContractError):
    pass


class OfflineContractError(MarkerError):
    pass


class SilentContractError(MarkerError):
    pass
