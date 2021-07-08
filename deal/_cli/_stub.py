from argparse import ArgumentParser
from pathlib import Path
from typing import List

from ..linter import StubsManager, generate_stub
from ._base import Command
from ._common import get_paths


class StubCommand(Command):
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

    @staticmethod
    def init_parser(parser: ArgumentParser) -> None:
        parser.add_argument('--iterations', type=int, default=1)
        parser.add_argument('paths', nargs='+')

    def __call__(self, args) -> int:
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
