# built-in
import sys
from argparse import ArgumentParser
from contextlib import contextmanager
from importlib import import_module
from pathlib import Path
from textwrap import indent
from traceback import format_exception
from typing import Iterator, Sequence, TextIO

import pygments
from pygments.formatters import TerminalFormatter
from pygments.lexers import PythonTracebackLexer

# app
from .._testing import cases
from ..linter._contract import Category
from ..linter._extractors.pre import format_call_args
from ..linter._func import Func
from ._common import get_paths
from .._colors import COLORS


@contextmanager
def sys_path(path: Path):
    path = str(path)
    sys.path.insert(0, path)
    try:
        yield
    finally:
        if sys.path[0] == path:
            del sys.path[0]


def has_pure_contract(func: Func) -> bool:
    for contract in func.contracts:
        if contract.category == Category.PURE:
            return True
        if contract.category == Category.HAS and not contract.args:
            return True
    return False


def get_func_names(path: Path) -> Iterator[str]:
    for func in Func.from_path(path=path):
        if has_pure_contract(func=func):
            yield func.name


def color_exception(text: str) -> str:
    text = text.replace('deal._exceptions.', '')
    return pygments.highlight(
        code=text,
        lexer=PythonTracebackLexer(),
        formatter=TerminalFormatter(),
    )


def print_exception(stream: TextIO) -> None:
    lines = format_exception(*sys.exc_info())
    text = color_exception(''.join(lines))
    text = indent(text=text, prefix='    ').rstrip()
    print(text, file=stream)


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
        print('  {blue}running {name}{end}'.format(name=func_name, **COLORS), file=stream)
        func = getattr(module, func_name)
        for case in cases(func=func, count=count):
            try:
                case()
            except Exception:
                line = '    {yellow}{name}({args}){end}'.format(
                    name=func_name,
                    args=format_call_args(args=case.args, kwargs=case.kwargs),
                    **COLORS,
                )
                print(line, file=stream)
                print_exception(stream=stream)
                failed += 1
                break
    return failed


def test_command(
    argv: Sequence[str], root: Path = None, stream: TextIO = sys.stdout,
) -> int:
    """Generate and run tests against pure functions.

    ```bash
    python3 -m deal test project/
    ```

    Function must be decorated by one of the following to be run:

    + `@deal.pure`
    + `@deal.has()` (without arguments)

    Options:

    + `--count`: how many input values combinations should be checked.

    Exit code is equal to count of failed test cases.
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
