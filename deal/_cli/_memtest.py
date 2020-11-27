# built-in
from contextlib import suppress
import sys
from argparse import ArgumentParser
from importlib import import_module
from pathlib import Path
from typing import Dict, Iterator, Sequence, TextIO

# app
from .._testing import cases, TestCase
from .._mem_test import MemoryTracker
from .._state import state
from ..linter._extractors.pre import format_call_args
from ._common import get_paths
from .._colors import COLORS
from ._test import sys_path, get_func_names


def run_tests(path: Path, root: Path, count: int, stream: TextIO = sys.stdout) -> int:
    names = list(get_func_names(path=path))
    if not names:
        return 0
    print('{magenta}running {path}{end}'.format(path=path, **COLORS), file=stream)
    module_name = '.'.join(path.relative_to(root).with_suffix('').parts)
    with sys_path(path=root):
        module = import_module(module_name)
    failed = 0
    for func_name in names:
        func = getattr(module, func_name)
        ok = run_cases(
            cases=cases(func=func, count=count, check_types=False),
            func_name=func_name,
            stream=stream,
            colors=COLORS,
        )
        if not ok:
            failed += 1
    return failed


def run_cases(
    cases: Iterator[TestCase],
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


def memtest_command(
    argv: Sequence[str], root: Path = None, stream: TextIO = sys.stdout,
) -> int:
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
    See [tests][tests] documentation for more details.

    [tests]: https://deal.readthedocs.io/basic/tests.html
    """
    if root is None:  # pragma: no cover
        root = Path()
    parser = ArgumentParser(prog='python3 -m deal test')
    parser.add_argument('--count', type=int, default=50)
    parser.add_argument('paths', nargs='+')
    args = parser.parse_args(argv)

    failed = 0
    for arg in args.paths:
        for path in get_paths(Path(arg)):
            failed += run_tests(
                path=Path(path),
                root=root,
                count=args.count,
                stream=stream,
            )
    return failed
