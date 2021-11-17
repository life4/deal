from argparse import ArgumentParser
from pathlib import Path

from .._colors import get_colors
from ..linter import TransformationType, Transformer
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
    + `--nocolor`: do not use colors in the console output.

    The exit code is always 0. If you want to test the code for missed decorators,
    use the `lint` command instead.
    """

    @staticmethod
    def init_parser(parser: ArgumentParser) -> None:
        parser.add_argument(
            '--types',
            nargs='*',
            choices=[tt.value for tt in TransformationType],
            default=['has', 'raises', 'safe', 'import'],
            help='types of decorators to apply',
        )
        parser.add_argument(
            '--double-quotes',
            action='store_true',
            help='use double quotes',
        )
        parser.add_argument('--nocolor', action='store_true', help='colorless output')
        parser.add_argument('paths', nargs='*', default='.')

    def __call__(self, args) -> int:
        types = {TransformationType(t) for t in args.types}
        colors = get_colors(args)
        for arg in args.paths:
            for path in get_paths(Path(arg)):
                self.print('{magenta}{path}{end}'.format(path=path, **colors))
                original_code = path.read_text(encoding='utf8')
                tr = Transformer(
                    content=original_code,
                    path=path,
                    types=types,
                )
                if args.double_quotes:
                    tr = tr._replace(quote='"')
                modified_code = tr.transform()
                if original_code == modified_code:
                    self.print('  {blue}no changes{end}'.format(**colors))
                else:
                    path.write_text(modified_code)
                    self.print('  {green}decorated{end}'.format(**colors))
        return 0
