import sys
from contextlib import suppress
from pathlib import Path
from typing import Any, Dict, Optional, Tuple, Type

from ._cached_property import cached_property
from ._colors import COLORS, NOCOLORS, highlight
from ._source import get_validator_source
from ._state import state


root = str(Path(__file__).parent)


def exception_hook(etype: Type[BaseException], value: BaseException, tb):
    """Exception hook to remove deal from the traceback for ContractError.
    """
    if not issubclass(etype, ContractError):
        return _excepthook(etype, value, tb)

    # try to reduce traceback by removing `deal` part
    prev_tb = patched_tb = tb
    while patched_tb:
        path: str = patched_tb.tb_frame.f_code.co_filename
        if path.startswith(root):
            with suppress(AttributeError):  # read-only attribute in <3.7
                prev_tb.tb_next = None
            break  # pragma: no cover
        prev_tb = patched_tb
        patched_tb = patched_tb.tb_next
    else:
        # cannot find deal in the trace, leave it as is
        patched_tb = tb

    return _excepthook(etype, value, patched_tb)


_excepthook = sys.excepthook
sys.excepthook = exception_hook


class ContractError(AssertionError):
    """The base class for all errors raised by deal contracts.
    """
    message: str
    errors: Optional[Any]
    validator: Any
    params: Dict[str, Any]
    origin: Optional[object]

    def __init__(
        self,
        message: str = '',
        errors=None,
        validator=None,
        params: Optional[Dict[str, Any]] = None,
        origin: Optional[object] = None,
    ) -> None:
        self.message = message
        self.errors = errors
        self.validator = validator
        self.params = params or {}
        self.origin = origin

        args = []
        if message:
            args.append(message)
        if errors:
            args.append(errors)
        super().__init__(*args)

    @cached_property
    def source(self) -> str:
        """The raw unformatted source code of the validator.
        """
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
        """The colored source code of the validator.
        """
        return highlight(self.source)

    @cached_property
    def variables(self) -> str:
        """Formatted variables passed into the validator.
        """
        sep = ', '
        colors = COLORS
        if not state.color:
            colors = NOCOLORS
        tmpl = '{blue}{k}{end}={magenta}{v}{end}'
        params = []
        for k, v in self.params.items():
            v = repr(v)
            if len(v) > 20:
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
            result += f' (where {self.variables})'
        return result


class PreContractError(ContractError):
    """The error raised by `deal.pre` for contract violation.
    """


class PostContractError(ContractError):
    """The error raised by `deal.post` for contract violation.
    """


class InvContractError(ContractError):
    """The error raised by `deal.inv` for contract violation.
    """


class ExampleContractError(ContractError):
    """The error raised by `deal.example` for contract violation.

    `deal.example` contracts are checked only during testing and linting,
    not at runtime.
    """


class RaisesContractError(ContractError):
    """The error raised by `deal.raises` for contract violation.
    """


class ReasonContractError(ContractError):
    """The error raised by `deal.reason` for contract violation.
    """


class MarkerError(ContractError):
    """The base class for errors raised by `deal.has` for contract violation.
    """


class OfflineContractError(MarkerError):
    """The error raised by `deal.has` for networking markers violation.

    The networking can be allowed by markers `io`, `network`, and `socket`.
    """


class SilentContractError(MarkerError):
    """The error raised by `deal.has` for printing markers violation.

    The printing can be allowed by markers `io`, `print`, `stdout`, and `stderr`.
    """


class NoMatchError(Exception):
    """The error raised by `deal.dispatch` when there is no matching implementation.

    "No matching implementation" means that all registered functions
    raised `PreContractError`.
    """
    __module__ = 'deal'

    def __init__(self, exceptions: Tuple[PreContractError, ...]) -> None:
        self.exceptions = exceptions

    def __str__(self) -> str:
        return '; '.join(str(e) for e in self.exceptions)


# Patch module name to show in repr `deal` instead of `deal._exceptions`
for cls in ContractError.__subclasses__():
    cls.__module__ = 'deal'
for cls in MarkerError.__subclasses__():
    cls.__module__ = 'deal'
