# built-in
import sys
from argparse import ArgumentParser
from importlib import import_module
from pathlib import Path
from traceback import format_exception
from typing import Iterator, Sequence, TextIO
from textwrap import indent

# app
from ..linter._contract import Category
from ..linter._func import Func
from .._testing import cases


COLORS = dict(
    red='\033[91m',
    green='\033[92m',
    yellow='\033[93m',
    blue='\033[94m',
    magenta='\033[95m',
    end='\033[0m',
)


def has_pure_contract(func: Func) -> bool:
    for contract in func.contracts:
        if contract.category == Category.PURE:
            return True
    return False


def get_func_names(path: Path) -> Iterator[str]:
    for func in Func.from_path(path=path):
        if has_pure_contract(func=func):
            yield func.name


def print_exception(stream: TextIO) -> None:
    lines = format_exception(*sys.exc_info())
    text = indent(text=''.join(lines), prefix='    ')
    text = '{red}{text}{end}'.format(text=text, **COLORS)
    print(text, file=stream)


def run_tests(path: Path, root: Path, count: int, stream: TextIO = sys.stdout) -> int:
    names = list(get_func_names(path=path))
    if not names:
        return 0
    print('{magenta}running {path}{end}'.format(path=path, **COLORS), file=stream)
    module_name = '.'.join(path.relative_to(root).with_suffix('').parts)
    module = import_module(module_name)
    failed = 0
    for func_name in names:
        print('  {blue}running {name}{end}'.format(name=func_name, **COLORS), file=stream)
        func = getattr(module, func_name)
        for case in cases(func=func, count=count):
            try:
                case()
            except Exception:
                print_exception(stream=stream)
                failed += 1
                break
    return failed


def test_command(argv: Sequence[str], root: Path = Path()) -> int:
    parser = ArgumentParser(prog='python3 -m deal test')
    parser.add_argument('--count', type=int, default=50)
    parser.add_argument('paths', nargs='+')
    args = parser.parse_args(argv)

    failed = 0
    for path in args.paths:
        failed += run_tests(
            path=Path(path),
            root=root,
            count=args.count,
        )
    return failed
