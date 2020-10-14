# built-in
import sys
import traceback
from argparse import ArgumentParser
from contextlib import contextmanager
from functools import update_wrapper
from importlib import import_module
from pathlib import Path
from textwrap import indent
from typing import Dict, Iterator, Sequence, TextIO, TypeVar

import pygments
from pygments.formatters import TerminalFormatter
from pygments.lexers import PythonTracebackLexer

# app
from .._testing import cases, TestCase
from ..linter._contract import Category
from ..linter._extractors.pre import format_call_args
from ..linter._func import Func
from ._common import get_paths
from .._colors import COLORS
from .._trace import trace, format_lines, TraceResult


T = TypeVar('T')


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


def format_exception() -> str:
    lines = traceback.format_exception(*sys.exc_info())
    text = color_exception(''.join(lines))
    text = indent(text=text, prefix='    ')
    return text.rstrip()


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
        # set `__wrapped__` attr so `trace` can find the original function.
        runner = update_wrapper(wrapper=run_cases, wrapped=func)
        tresult = trace(
            func=runner,
            cases=fast_iterator(cases(func=func, count=count)),
            func_name=func_name,
            count=count,
            stream=stream,
        )
        if tresult.func_result and tresult.all_lines:
            text = format_coverage(tresult=tresult, colors=COLORS)
            print(text, file=stream)
        else:
            failed += 1
    return failed


def fast_iterator(iterator: Iterator[T]) -> Iterator[T]:
    """
    Iterate over `iterator` disabling tracer on every iteration step.
    This is a trick to avoid using our coverage tracer when calling hypothesis machinery.
    Without it, testing is about 3 times slower.
    """
    default_trace = sys.gettrace()
    while True:
        sys.settrace(None)
        try:
            case = next(iterator)
        except StopIteration:
            return
        finally:
            sys.settrace(default_trace)
        yield case


def run_cases(cases: Iterator[TestCase], func_name: str, count: int, stream: TextIO) -> bool:
    print('  {blue}running {name}{end}'.format(name=func_name, **COLORS), file=stream)
    for case in cases:
        try:
            case()
        except Exception:
            line = '    {yellow}{name}({args}){end}'.format(
                name=func_name,
                args=format_call_args(args=case.args, kwargs=case.kwargs),
                **COLORS,
            )
            print(line, file=stream)
            print(format_exception(), file=stream)
            return False
    return True


def format_coverage(tresult: TraceResult, colors: Dict[str, str]) -> str:
    cov = tresult.coverage
    if cov >= 85:
        color = colors['green']
    elif cov >= 50:
        color = colors['yellow']
    else:
        color = colors['red']
    tmpl = '    coverage {color}{cov}%{end}'
    missing = format_lines(
        statements=tresult.all_lines,
        lines=tresult.all_lines - tresult.covered_lines,
    )
    if cov != 0 and cov != 100 and len(missing) <= 60:
        tmpl += ' (missing {missing})'
    line = tmpl.format(
        cov=cov,
        color=color,
        missing=missing,
        **colors,
    )
    return line


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
