from argparse import ArgumentParser
from contextlib import suppress
from importlib import import_module
from pathlib import Path
from typing import Dict, Iterable, TextIO

from .._colors import COLORS
from .._mem_test import MemoryTracker
from .._state import state
from .._testing import TestCase, cases
from ..linter._extractors.pre import format_call_args
from ._base import Command
from ._common import get_paths
from ._test import get_func_names, sys_path


def run_cases(
    cases: Iterable[TestCase],
    func_name: str,
    stream: TextIO,
    colors: Dict[str, str],
) -> bool:
    print('  {blue}running {name}{end}'.format(name=func_name, **colors), file=stream)
    for case in cases:
        tracker = MemoryTracker()
        debug = state.debug
        state.disable()
        try:
            with tracker, suppress(Exception):
                case()
        finally:
            state.debug = debug
        if not tracker.diff:
            continue

        # show the diff and stop testing the func
        line = '    {yellow}{name}({args}){end}'.format(
            name=func_name,
            args=format_call_args(args=case.args, kwargs=case.kwargs),
            **colors,
        )
        print(line, file=stream)
        longest_name_len = max(len(name) for name in tracker.diff)
        for name, count in tracker.diff.items():
            line = '      {red}{name}{end} x{count}'.format(
                name=name.ljust(longest_name_len),
                count=count,
                **colors,
            )
            print(line, file=stream)
        return False
    return True


class MemtestCommand(Command):
    """Generate and run tests against pure functions and report memory leaks.

    ```bash
    python3 -m deal memtest project/
    ```

    Function must be decorated by one of the following to be run:

    + `@deal.pure`
    + `@deal.has()` (without arguments)

    Options:

    + `--count`: how many input values combinations should be checked.

    Exit code is equal to count of leaked functions.
    See [memory leaks][leaks] documentation for more details.

    [leaks]: https://deal.readthedocs.io/details/tests.html#memory-leaks
    """

    @staticmethod
    def init_parser(parser: ArgumentParser) -> None:
        parser.add_argument('--count', type=int, default=50)
        parser.add_argument('paths', nargs='+')

    def __call__(self, args) -> int:
        failed = 0
        for arg in args.paths:
            for path in get_paths(Path(arg)):
                failed += self.run_tests(
                    path=Path(path),
                    count=args.count,
                )
        return failed

    def run_tests(self, path: Path, count: int) -> int:
        names = list(get_func_names(path=path))
        if not names:
            return 0
        self.print('{magenta}running {path}{end}'.format(path=path, **COLORS))
        module_name = '.'.join(path.relative_to(self.root).with_suffix('').parts)
        with sys_path(path=self.root):
            module = import_module(module_name)
        failed = 0
        for func_name in names:
            func = getattr(module, func_name)
            ok = run_cases(
                cases=cases(func=func, count=count, check_types=False),
                func_name=func_name,
                stream=self.stream,
                colors=COLORS,
            )
            if not ok:
                failed += 1
        return failed
