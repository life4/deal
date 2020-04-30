# built-in
from argparse import ArgumentParser
from pathlib import Path
from typing import Sequence

# app
from ..linter import StubsManager, generate_stub


def stub_command(argv: Sequence[str]) -> int:
    parser = ArgumentParser(prog='python3 -m deal stub')
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
