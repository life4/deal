from argparse import ArgumentParser
from pathlib import Path

from ..linter import Transformer, TransformationType
from ._base import Command
from ._common import get_paths


class DecorateCommand(Command):
    """Add decorators to your code.

    ```bash
    python3 -m deal decorate project/
    ```

    Options:
    + `--types`: types of decorators to apply. All are enabled by default.
    + `--double-quotes`: use double quotes. Single quotes are used by default.

    The exit code is always 0. If you want to test the code for missed decorators,
    use the `lint` command instead.
    """

    @staticmethod
    def init_parser(parser: ArgumentParser) -> None:
        parser.add_argument(
            '--types',
            nargs='*',
            choices=[tt.value for tt in TransformationType],
            default=['has', 'raises', 'safe'],
            help='types of decorators to apply',
        )
        parser.add_argument(
            '--double-quotes',
            action='store_true',
            help='use double quotes',
        )
        parser.add_argument('paths', nargs='*', default='.')

    def __call__(self, args) -> int:
        types = {TransformationType(t) for t in args.types}
        for arg in args.paths:
            for path in get_paths(Path(arg)):
                self.print(path)
                tr = Transformer(path=path, types=types)
                if args.double_quotes:
                    tr = tr._replace(quote='"')
                content = tr.transform()
                path.write_text(content)
        return 0
