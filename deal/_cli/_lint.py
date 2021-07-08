import ast
import json
from argparse import ArgumentParser
from pathlib import Path
from textwrap import dedent, indent
from typing import Iterable, Iterator

from .._colors import get_colors, highlight
from ..linter import Checker
from ._base import Command
from ._common import get_paths


TEMPLATE = '  {blue}{row}{end}:{blue}{col}{end} {magenta}{code}{end} {yellow}{text}{end}'
VALUE = ' {magenta}({value}){end}'
POINTER = '{magenta}^{end}'


class LintCommand(Command):
    """Run linter against the given files.

    ```bash
    python3 -m deal lint project/
    ```

    Options:

    + `--json`: output violations as [json per line][ndjson].
    + `--nocolor`: output violations in human-friendly format but without colors.
      Useful for running linter on CI.

    Exit code is equal to the found violations count.
    See [linter][linter] documentation for more details.

    [ndjson]: http://ndjson.org/
    [linter]: https://deal.readthedocs.io/basic/linter.html
    """

    @staticmethod
    def init_parser(parser: ArgumentParser) -> None:
        parser.add_argument('--json', action='store_true', help='json output')
        parser.add_argument('--nocolor', action='store_true', help='colorless output')
        parser.add_argument('paths', nargs='*', default='.')

    def __call__(self, args) -> int:
        prev = None
        errors = list(self.get_errors(paths=args.paths))
        colors = get_colors(args)
        for error in errors:
            if args.json:
                self.print(json.dumps(error))
                continue

            # print file path
            if error['path'] != prev:
                self.print('{green}{path}{end}'.format(**colors, **error))
            prev = error['path']

            # print message
            line = TEMPLATE.format(**colors, **error)
            if error['value']:
                line += VALUE.format(**colors, **error)
            self.print(line)

            # print code line
            pointer = ' ' * error['col'] + POINTER.format(**colors)
            content = error['content']
            if not args.nocolor:
                content = highlight(content)
            content += '\n' + pointer
            content = indent(dedent(content), prefix='    ')
            self.print(content)
        return len(errors)

    @staticmethod
    def get_errors(paths: Iterable[str]) -> Iterator[dict]:
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
