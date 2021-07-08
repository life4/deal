from argparse import ArgumentParser
from pathlib import Path
from typing import Dict, Iterator, TextIO

import astroid
from deal_solver import Conclusion, Contract, Theorem

from .._colors import get_colors
from ..linter._extractors import get_contracts
from ._base import Command
from ._common import get_paths


TEMPLATE_MOD = '{blue}{name}{end}'
TEMPLATE_FUN = '  {magenta}{name}{end}'
TEMPLATE_CON = '    {color}{p.conclusion.value}{end} {p}'


class DealTheorem(Theorem):
    @staticmethod
    def get_contracts(func: astroid.FunctionDef) -> Iterator[Contract]:
        if not func.decorators:
            return
        for name, args in get_contracts(func.decorators.nodes):
            yield Contract(name=name, args=args)


def run_solver(
    path: Path,
    stream: TextIO,
    show_skipped: bool,
    colors: Dict[str, str],
) -> int:
    file_name_shown = False
    text = path.read_text()
    theorems = DealTheorem.from_text(text)
    failed_count = 0
    for theorem in theorems:
        if theorem.name.startswith('test_'):
            continue

        proof = theorem.prove()
        assert proof.conclusion is not None
        if proof.conclusion == Conclusion.SKIP and not show_skipped:
            continue

        if not file_name_shown:
            line = TEMPLATE_MOD.format(name=path, **colors)
            print(line, file=stream)
            file_name_shown = True

        line = TEMPLATE_FUN.format(name=theorem.name, **colors)
        print(line, file=stream)
        line = TEMPLATE_CON.format(p=proof, color=colors[proof.color], **colors)
        print(line, file=stream)
        failed_count += proof.conclusion == Conclusion.FAIL
    return failed_count


class ProveCommand(Command):
    """Verify correctness of code.

    ```bash
    python3 -m deal prove project/
    ```

    Options:

    + `--skipped`: show skipped functions.
    + `--nocolor`: disable colored output.

    Exit code is equal to the failed theorems count.
    See [Formal Verification][verification] documentation for more information.

    [verification]: https://deal.readthedocs.io/details/verification.html
    """

    @staticmethod
    def init_parser(parser: ArgumentParser) -> None:
        parser.add_argument('--skipped', action='store_true', help='show skipped')
        parser.add_argument('--nocolor', action='store_true', help='colorless output')
        parser.add_argument('paths', nargs='+')

    def __call__(self, args) -> int:
        colors = get_colors(args)

        failed = 0
        for arg in args.paths:
            for path in get_paths(Path(arg)):
                failed += run_solver(
                    path=path,
                    stream=self.stream,
                    show_skipped=args.skipped,
                    colors=colors,
                )
        return failed
