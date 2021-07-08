
from typing import Dict
import pygments
from pygments.formatters import TerminalFormatter
from pygments.lexers import PythonLexer
from ._state import state


COLORS = dict(
    red='\033[91m',
    green='\033[92m',
    yellow='\033[93m',
    blue='\033[94m',
    magenta='\033[95m',
    end='\033[0m',
)
NOCOLORS = dict(
    red='',
    green='',
    yellow='',
    blue='',
    magenta='',
    end='',
)


def highlight(source: str) -> str:
    source = pygments.highlight(
        code=source,
        lexer=PythonLexer(),
        formatter=TerminalFormatter(),
    )
    return source.rstrip()


def get_colors(args) -> Dict[str, str]:
    if not state.color:
        return NOCOLORS
    if args.nocolor:
        state.color = False
        return NOCOLORS
    return COLORS
