import sys
from pathlib import Path
from typing import Any, Optional
from inspect import getsourcelines

import pygments
from pygments.formatters.terminal import TerminalFormatter
from pygments.lexers.python import PythonLexer

from ._cached_property import cached_property

root = str(Path(__file__).parent)


def exception_hook(etype: type, value, tb):
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
    message: str
    errors: Optional[Any]
    validator: Any

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
        source = self._source_from_code()
        if source:
            return source
        if hasattr(self.validator, '__qualname__'):
            return self.validator.__qualname__
        return repr(self.validator)

    def _source_from_code(self) -> Optional[str]:
        if not hasattr(self.validator, '__code__'):
            return None
        try:
            lines, _ = getsourcelines(self.validator.__code__)
        except OSError:
            return None
        if not lines:
            return None
        line = lines[0].strip()
        if line.startswith('@'):
            _, sep, line = line.partition('(')
            if sep and line.endswith(')'):
                line = line[:-1]
        if line.startswith('lambda'):
            _, _, line = line.partition(':')
        return line.strip()

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
