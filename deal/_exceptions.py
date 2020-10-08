import sys
from pathlib import Path
from typing import Any, Dict, Optional

import pygments
from pygments.formatters.terminal import TerminalFormatter
from pygments.lexers.python import PythonLexer

from ._cached_property import cached_property
from ._source import get_validator_source
from ._state import state
from ._colors import COLORS, NOCOLORS

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
    params: Dict[str, Any]

    def __init__(
        self,
        message: str = '',
        errors=None,
        validator=None,
        params: Dict[str, Any] = None,
    ) -> None:
        self.message = message
        self.errors = errors
        self.validator = validator
        self.params = params or {}

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
        source = get_validator_source(self.validator)
        if source:
            return source
        if hasattr(self.validator, '__name__'):
            return self.validator.__name__
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

    @cached_property
    def variables(self) -> str:
        sep = ', '
        colors = COLORS
        if not state.color:
            colors = NOCOLORS
        tmpl = '{blue}{k}{end}={magenta}{v}{end}'
        params = []
        for k, v in self.params.items():
            v = repr(v)
            if len(v) > 10:
                continue
            params.append(tmpl.format(k=k, v=v, **colors))
        return sep.join(params)

    def __str__(self) -> str:
        result = self.message
        if not result and self.errors:
            result = repr(self.errors)
        if not result and self.source:
            result = 'expected '
            if state.color:
                result += self.colored_source
            else:
                result += self.source
        if self.variables:
            if result:
                result += ' (where {})'.format(self.variables)
            else:
                result += self.variables
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
