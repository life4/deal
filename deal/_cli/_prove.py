# built-in
import sys
from argparse import ArgumentParser
from pathlib import Path
from typing import Sequence, TextIO

from deal_solver import Conclusion, Theorem

# app
from .._colors import COLORS
from ._common import get_paths


TEMPLATE_MOD = '{blue}{name}{end}'
TEMPLATE_FUN = '  {magenta}{name}{end}'
TEMPLATE_CON = '    {color}{c.value}{end} {e}'


def run_solver(path: Path, stream, show_skipped: bool):
    file_name_shown = False
    text = path.read_text()
    theorems = Theorem.from_text(text)
    failed_count = 0
    for theorem in theorems:
        if theorem.name.startswith('test_'):
            continue

        theorem.prove()
        assert theorem.conclusion is not None
        if theorem.conclusion == Conclusion.SKIP and not show_skipped:
            continue

        if not file_name_shown:
            line = TEMPLATE_MOD.format(name=path, **COLORS)
            print(line, file=stream)
            file_name_shown = True

        line = TEMPLATE_FUN.format(name=theorem.name, **COLORS)
        print(line, file=stream)

        color = COLORS[theorem.conclusion.color]
        descr = theorem.example or ''
        if theorem.error:
            descr = ' '.join([str(arg) for arg in theorem.error.args])
            descr = ' '.join(descr.split())[:80]
        line = TEMPLATE_CON.format(
            c=theorem.conclusion,
            e=descr,
            color=color,
            **COLORS,
        )
        print(line, file=stream)
        failed_count += theorem.conclusion == Conclusion.FAIL
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
                path=Path(path),
                stream=stream,
                show_skipped=args.skipped,
            )
    return failed
