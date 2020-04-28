from argparse import ArgumentParser
from pathlib import Path
from typing import Sequence


def get_parser() -> ArgumentParser:
    parser = ArgumentParser(prog='python3 -m deal')
    parser.add_argument('command', choices=['lint', 'stub'])
    return parser


def lint(argv: Sequence[str]) -> int:
    from .linter._cli import main as linter_main
    return linter_main(argv=argv)


def stub(argv: Sequence[str]) -> int:
    from .linter._stub import generate_stub
    for path in argv:
        path = Path(path)
        generate_stub(path=path)
    return 0


COMMANDS = dict(lint=lint, stub=stub)


def main(argv: Sequence[str]) -> int:
    parser = get_parser()
    args, unknown = parser.parse_known_args(argv)
    command = COMMANDS[args.command]
    return command(unknown)
