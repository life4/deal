# built-in
from argparse import ArgumentParser
from pathlib import Path
from typing import List, Sequence

# app
from ..linter import StubsManager, generate_stub
from ._common import get_paths


def stub_command(argv: Sequence[str]) -> int:
    parser = ArgumentParser(prog='python3 -m deal stub')
    parser.add_argument('--iterations', type=int, default=1)
    parser.add_argument('paths', nargs='+')
    args = parser.parse_args(argv)

    paths: List[Path] = []
    for arg in args.paths:
        for path in get_paths(Path(arg)):
            paths.append(path)

    roots = list(StubsManager.default_paths) + list(set(paths))
    stubs = StubsManager(paths=roots)

    for _ in range(args.iterations):
        for path in paths:
            generate_stub(path=path, stubs=stubs)
    return 0
