# built-in
from argparse import ArgumentParser
from pathlib import Path
from typing import List, Sequence

# app
from ..linter import StubsManager, generate_stub
from ._common import get_paths


def stub_command(argv: Sequence[str]) -> int:
    """Generate stub files for the given Python files.

    ```bash
    python3 -m deal stub project/
    ```

    Options:

    + `--iterations`: how many time run stub generation against files.
      Every new iteration uses results from the previous ones, improving the result.
      Default: 1.

    Exit code is 0. See [stubs][stubs] documentation for more details.

    [stubs]: https://deal.readthedocs.io/details/stubs.html
    """
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
