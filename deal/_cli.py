from argparse import ArgumentParser
from pathlib import Path
from typing import Sequence

from .linter._stub import generate_stub, StubsManager


def get_parser() -> ArgumentParser:
    parser = ArgumentParser(prog='python3 -m deal')
    parser.add_argument('command', choices=['lint', 'stub'])
    return parser


def lint(argv: Sequence[str]) -> int:
    from .linter._cli import main as linter_main
    return linter_main(argv=argv)


def stub(argv: Sequence[str]) -> int:
    parser = ArgumentParser(prog='python3 -m deal')
    parser.add_argument('--iterations', type=int, default=1)
    parser.add_argument('paths', nargs='+')
    args = parser.parse_args(argv)

    paths = [Path(path) for path in args.paths]
    roots = list(StubsManager.default_paths) + list(set(paths))
    stubs = StubsManager(paths=roots)

    for _ in range(args.iterations):
        for path in paths:
            generate_stub(path=path, stubs=stubs)
    return 0


COMMANDS = dict(lint=lint, stub=stub)


def main(argv: Sequence[str]) -> int:
    parser = get_parser()
    args, unknown = parser.parse_known_args(argv)
    command = COMMANDS[args.command]
    return command(unknown)
