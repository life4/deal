# built-in
import ast
import json
from argparse import ArgumentParser
from pathlib import Path
from textwrap import dedent, indent
from typing import Iterable, Iterator, Sequence, Union

# app
from ..linter import Checker


try:
    import pygments
except ImportError:
    pygments = None
else:
    from pygments.formatters import TerminalFormatter
    from pygments.lexers import PythonLexer


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
TEMPLATE = '  {blue}{row}{end}:{blue}{col}{end} {magenta}{code}{end} {yellow}{text}{end}'
VALUE = ' {magenta}({value}){end}'
POINTER = '{magenta}^{end}'


def highlight(source: str) -> str:
    if pygments is None:
        return source
    source = pygments.highlight(
        code=source,
        lexer=PythonLexer(),
        formatter=TerminalFormatter(),
    )
    return source.strip()


def get_paths(path: Path) -> Iterator[Path]:
    """Recursively yields python files.
    """
    if not path.exists():
        raise FileNotFoundError(str(path))
    if path.is_file():
        if path.suffix == '.py':
            yield path
        return
    for subpath in path.iterdir():
        if subpath.name[0] == '.':
            continue
        if subpath.name == '__pycache__':
            continue
        yield from get_paths(subpath)


def get_errors(paths: Iterable[Union[str, Path]]) -> Iterator[dict]:
    for arg in paths:
        for path in get_paths(Path(arg)):
            content = path.read_text()
            checker = Checker(
                filename=str(path),
                tree=ast.parse(content),
            )
            lines = content.split('\n')
            for error in checker.get_errors():
                yield dict(
                    path=str(path),
                    row=error.row,
                    col=error.col,
                    code=error.full_code,
                    text=error.text,
                    value=error.value,
                    content=lines[error.row - 1],
                )


def get_parser() -> ArgumentParser:
    parser = ArgumentParser(prog='python3 -m deal lint')
    parser.add_argument('--json', action='store_true', help='json output')
    parser.add_argument('--nocolor', action='store_true', help='colorless output')
    parser.add_argument('paths', nargs='*', default='.')
    return parser


def lint_command(argv: Sequence[str]) -> int:
    parser = get_parser()
    args = parser.parse_args(argv)
    prev = None
    errors = list(get_errors(paths=args.paths))
    colors = COLORS
    if args.nocolor:
        colors = NOCOLORS
    for error in errors:
        if args.json:
            print(json.dumps(error))
            continue

        # print file path
        if error['path'] != prev:
            print('{green}{path}{end}'.format(**colors, **error))
        prev = error['path']

        # print message
        line = TEMPLATE.format(**colors, **error)
        if error['value']:
            line += VALUE.format(**colors, **error)
        print(line)

        # print code line
        pointer = ' ' * error['col'] + POINTER.format(**colors)
        content = error['content']
        if not args.nocolor:
            content = highlight(content)
        content += '\n' + pointer
        content = indent(dedent(content), prefix='    ')
        print(content)
    return len(errors)
