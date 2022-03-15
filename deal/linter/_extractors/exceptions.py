import ast
import builtins
import re
from inspect import cleandoc
from itertools import zip_longest
from typing import Iterator, Optional, Union

import astroid

from .._contract import Category
from .._stub import StubsManager
from .common import TOKENS, Extractor, Token, get_full_name, get_name, get_stub, infer
from .contracts import get_contracts

try:
    import docstring_parser
except ImportError:
    docstring_parser = None  # type: ignore[assignment]


get_exceptions = Extractor()
REX_GOOGLE_SECTION = re.compile(r'[A-Z][a-z]+:\s*')


@get_exceptions.register(*TOKENS.ASSERT)
def handle_assert(expr, **kwargs) -> Optional[Token]:
    return Token(value=AssertionError)


# explicit raise
@get_exceptions.register(*TOKENS.RAISE)
def handle_raise(expr: ast.Raise, **kwargs) -> Optional[Token]:
    if expr.exc is None:
        return None
    name = get_name(expr.exc)
    if not name:
        # raised a value, too tricky
        if not isinstance(expr.exc, TOKENS.CALL):
            return None
        # raised an instance of an exception
        name = get_name(expr.exc.func)
        if not name or name[0].islower():
            return None
    exc = getattr(builtins, name, name)
    return Token(value=exc, line=expr.exc.lineno, col=expr.exc.col_offset)


# division by zero
@get_exceptions.register(*TOKENS.BIN_OP)
def handle_bin_op(expr: Union[ast.BinOp, astroid.BinOp], **kwargs) -> Optional[Token]:
    if isinstance(expr.op, ast.Div) or expr.op == '/':
        if isinstance(expr.right, astroid.NodeNG):
            guesses = infer(expr=expr.right)
            for guess in guesses:
                if type(guess) is not astroid.Const:
                    continue
                return Token(value=ZeroDivisionError, col=expr.right.col_offset)
        if isinstance(expr.right, ast.Num) and expr.right.n == 0:
            return Token(value=ZeroDivisionError, col=expr.right.col_offset)
    return None


@get_exceptions.register(*TOKENS.CALL)
def handle_call(
    expr: Union[ast.Call, astroid.Call],
    dive: bool = True,
    stubs: Optional[StubsManager] = None,
) -> Iterator[Token]:
    # exit()
    name = get_name(expr.func)
    if name and name == 'exit':
        yield Token(value=SystemExit)
    # sys.exit()
    if isinstance(expr.func, TOKENS.ATTR):
        name = get_name(expr.func)
        if name and name == 'sys.exit':
            yield Token(value=SystemExit)

    stubs_found = False
    if type(expr) is astroid.Call and stubs is not None:
        for token in _exceptions_from_stubs(expr=expr, stubs=stubs):
            stubs_found = True
            yield token

    # Infer function call and check the function body for raises.
    # Do not dive into called function if we already found stubs for it.
    if not stubs_found and dive:
        yield from _exceptions_from_func(expr=expr)


def _exceptions_from_stubs(expr: astroid.Call, stubs: StubsManager) -> Iterator[Token]:
    for value in infer(expr=expr.func):
        if type(value) is not astroid.FunctionDef:
            continue
        module_name, func_name = get_full_name(expr=value)
        stub = get_stub(module_name=module_name, expr=value, stubs=stubs)
        if stub is None:
            continue
        names = stub.get(func=func_name, contract=Category.RAISES)
        for name in names:
            name = getattr(builtins, name, name)
            yield Token(value=name)


def _exceptions_from_func(expr: Union[ast.Call, astroid.Call]) -> Iterator[Token]:
    for value in infer(expr.func):
        if type(value) is not astroid.FunctionDef:
            continue

        # recursively infer exceptions from the function body
        for error in get_exceptions(body=value.body, dive=False):
            yield Token(value=error.value)

        # get explicitly specified exceptions from `@deal.raises`
        name: Optional[str]
        for contract in get_contracts(value):
            if contract.name != 'raises':
                continue
            for arg in contract.args:
                name = get_name(arg)
                if name is None:
                    continue
                name = getattr(builtins, name, name)
                yield Token(value=name)

        # get exceptions from the docstring
        name: str
        for name in _excs_from_doc(value.doc):
            name = getattr(builtins, name, name)
            yield Token(value=name)
    return None


# TODO: use it on the target function docstring too
def _excs_from_doc(doc: Optional[str]) -> Iterator[str]:
    if doc is None:
        return

    if docstring_parser is not None:
        parsed = docstring_parser.parse(doc)
        for exc_info in parsed.raises:
            if exc_info.type_name:
                yield exc_info.type_name
        return

    google_section = ''
    numpy_section = ''
    lines = cleandoc(doc).splitlines()
    for line, next_line in zip_longest(lines, lines[1:]):
        words = line.split()
        if not words:
            continue

        # sphinx and epydoc docstring
        if len(words) >= 2 and words[0] in (':raises', '@raise'):
            yield words[1].rstrip(':')
            continue

        # google docstring
        if REX_GOOGLE_SECTION.fullmatch(line):
            google_section = line.strip().rstrip(':').lower()
            continue
        indent = len(line) - len(line.lstrip())
        if google_section == 'raises' and indent == 4:
            yield words[0].rstrip(':')
            continue

        # numpy docstring
        if next_line is not None:
            next_line = next_line.strip()
            if _is_header_highlight(next_line):
                numpy_section = line.strip().rstrip(':').lower()
                continue
        if _is_header_highlight(line):
            continue
        if numpy_section == 'raises' and line == line.lstrip() and indent == 0:
            yield line.rstrip()


def _is_header_highlight(line: str) -> bool:
    line = line.strip()
    return len(set(line)) == 1 and line[0] in '-+'
