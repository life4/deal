# built-in
import sys
from argparse import ArgumentParser
from pathlib import Path
from typing import Iterator, Sequence, TextIO

import astroid
from deal_solver import Conclusion, Contract, Theorem

# app
from .._colors import COLORS
from ._common import get_paths
from ..linter._extractors import get_contracts


TEMPLATE_MOD = '{blue}{name}{end}'
TEMPLATE_FUN = '  {magenta}{name}{end}'
TEMPLATE_CON = '    {color}{p.conclusion}{end} {p}'


class DealTheorem(Theorem):
    @staticmethod
    def get_contracts(func: astroid.FunctionDef) -> Iterator[Contract]:
        if not func.decorators:
            return
        for name, args in get_contracts(func.decorators.nodes):
            yield Contract(name=name, args=args)


def run_solver(path: Path, stream: TextIO, show_skipped: bool) -> int:
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
            line = TEMPLATE_MOD.format(name=path, **COLORS)
            print(line, file=stream)
            file_name_shown = True

        line = TEMPLATE_FUN.format(name=theorem.name, **COLORS)
        print(line, file=stream)
        line = TEMPLATE_CON.format(p=proof, color=COLORS[proof.color], **COLORS)
        print(line, file=stream)
        failed_count += proof.conclusion == Conclusion.FAIL
    return failed_count


def prove_command(
    argv: Sequence[str], root: Path = None, stream: TextIO = sys.stdout,
) -> int:
    """
    ...
    """
    if root is None:  # pragma: no cover
        root = Path()
    parser = ArgumentParser(prog='python3 -m deal prove')
    parser.add_argument('--skipped', action='store_true', help='show skipped')
    parser.add_argument('paths', nargs='+')
    args = parser.parse_args(argv)

    failed = 0
    for arg in args.paths:
        for path in get_paths(Path(arg)):
            failed += run_solver(
                path=path,
                stream=stream,
                show_skipped=args.skipped,
            )
    return failed
