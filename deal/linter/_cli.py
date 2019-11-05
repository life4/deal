import ast
from pathlib import Path
from textwrap import dedent, indent
from typing import Iterable, Iterator

from ._checker import Checker


COLORS = dict(
    red='\033[91m',
    green='\033[92m',
    yellow='\033[93m',
    blue='\033[94m',
    magenta='\033[95m',
    end='\033[0m',
)
TEMPLATE = '  {blue}{row}{end}:{blue}{col}{end} {yellow}{text}{end}'
POINTER = '{magenta}^{end}'


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


def get_errors(argv: Iterable) -> Iterator[dict]:
    for arg in argv:
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
                    code=error.code,
                    text=error.text,
                    content=lines[error.row - 1],
                )


def main(argv: Iterable) -> int:
    errors = list(get_errors(argv=argv))
    prev = None
    for error in errors:
        if error['path'] != prev:
            print('{green}{path}{end}'.format(**COLORS, **error))
        print(TEMPLATE.format(**COLORS, **error))
        pointer = ' ' * error['col'] + POINTER.format(**COLORS)
        content = error['content'] + '\n' + pointer
        content = indent(dedent(content), prefix='    ')
        print(content)
    return len(errors)
