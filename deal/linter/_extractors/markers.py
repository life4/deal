import ast
from typing import Optional, Iterator

# external
import astroid

# app
from .common import TOKENS, Extractor, Token, get_name, infer, get_full_name, get_stub
from .contracts import get_contracts
from .value import get_value
from .._contract import Category
from .._stub import StubsManager


get_markers = Extractor()


@get_markers.register(*TOKENS.GLOBAL)
def handle_global(expr, **kwargs) -> Optional[Token]:
    return Token(marker='global', line=expr.lineno, col=expr.col_offset)


@get_markers.register(*TOKENS.NONLOCAL)
def handle_nonlocal(expr, **kwargs) -> Optional[Token]:
    return Token(marker='global', line=expr.lineno, col=expr.col_offset)


@get_markers.register(ast.Import)
def handle_ast_import(expr: ast.Import, **kwargs) -> Optional[Token]:
    return Token(marker='import', line=expr.lineno, col=expr.col_offset)


@get_markers.register(astroid.Import)
def handle_astroid_import(expr: astroid.Import, **kwargs) -> Optional[Token]:
    return Token(marker='import', line=expr.lineno, col=expr.col_offset)


@get_markers.register(ast.ImportFrom)
def handle_ast_import_from(expr: ast.ImportFrom, **kwargs) -> Optional[Token]:
    return Token(marker='import', line=expr.lineno, col=expr.col_offset)


@get_markers.register(astroid.ImportFrom)
def handle_astroid_import_from(expr: astroid.ImportFrom, **kwargs) -> Optional[Token]:
    return Token(marker='import', line=expr.lineno, col=expr.col_offset)


@get_markers.register(*TOKENS.CALL)
def handle_call(expr, dive: bool = True, stubs: StubsManager = None) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    name = get_name(expr.func)

    # stdout and stderr
    if name == 'print':
        yield Token(marker='stdout', value='print', **token_info)
        return
    if name in ('print', 'sys.stdout', 'sys.stdout.write'):
        yield Token(marker='stdout', value='sys.stdout', **token_info)
        return
    if name in ('sys.stderr', 'sys.stderr.write'):
        yield Token(marker='stderr', value='sys.stderr', **token_info)
        return

    # read and write
    if name == 'open':
        if _is_open_to_write(expr):
            yield Token(marker='write', value='open', **token_info)
        else:
            yield Token(marker='read', value='open', **token_info)
        return
    if _is_pathlib_write(expr):
        yield Token(marker='write', value='Path.open', **token_info)
        return

    stubs_found = False
    if type(expr) is astroid.Call and stubs is not None:
        for token in _markers_from_stubs(expr=expr, stubs=stubs):
            stubs_found = True
            yield token

    # Infer function call and check the function body for raises.
    # Do not dive into called function if we already found stubs for it.
    if not stubs_found and dive:
        yield from _markers_from_func(expr=expr)


@get_markers.register(*TOKENS.WITH)
def handle_with(expr) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    for item in expr.items:
        if isinstance(item, ast.withitem):
            item = item.context_expr
        else:
            item = item[0]
        if _is_pathlib_write(item):
            return Token(marker='write', value='Path.open', **token_info)
        if not isinstance(item, TOKENS.CALL):
            continue
        name = get_name(item.func)
        if name == 'open':
            if _is_open_to_write(item):
                return Token(marker='write', value='open', **token_info)
            return Token(marker='read', value='open', **token_info)
    return None


def _is_open_to_write(expr) -> bool:
    for arg in expr.args:
        if isinstance(arg, astroid.Const) and arg.value == 'w':
            return True
        if isinstance(arg, ast.Str) and 'w' in arg.s:
            return True

    if not expr.keywords:
        return False
    for arg in expr.keywords:
        if arg.arg != 'mode':
            continue
        if isinstance(arg.value, astroid.Const) and 'w' in arg.value.value:
            return True
        if isinstance(arg.value, ast.Str) and 'w' in arg.value.s:
            return True
    return False


def _is_pathlib_write(expr) -> bool:
    if not isinstance(expr, astroid.Call):
        return False
    if not isinstance(expr.func, astroid.Attribute):
        return False
    if expr.func.attrname not in ('write_text', 'write_bytes', 'open'):
        return False

    # if it's open, check that mode is "w"
    if expr.func.attrname == 'open':
        if not _is_open_to_write(expr):
            return False

    for value in infer(expr.func.expr):
        if isinstance(value, astroid.Instance):
            if value.pytype().startswith('pathlib.'):
                return True
    return False


def _markers_from_stubs(expr: astroid.Call, stubs: StubsManager) -> Iterator[Token]:
    for value in infer(expr=expr.func):
        if type(value) is not astroid.FunctionDef:
            continue
        module_name, func_name = get_full_name(expr=value)
        stub = get_stub(module_name=module_name, expr=value, stubs=stubs)
        if stub is None:
            continue
        names = stub.get(func=func_name, contract=Category.HAS)
        for name in names:
            yield Token(value=name, line=expr.lineno, col=expr.col_offset)


def _markers_from_func(expr) -> Iterator[Token]:
    for value in infer(expr.func):
        if type(value) is not astroid.FunctionDef:
            continue

        # recursively infer markers from the function body
        for error in get_markers(body=value.body, dive=False):
            yield Token(value=error.value, line=expr.lineno, col=expr.col_offset)

        # get explicitly specified markers from `@deal.has`
        if not value.decorators:
            continue
        for category, args in get_contracts(value.decorators.nodes):
            if category != 'has':
                continue
            for arg in args:
                value = get_value(arg)
                if type(value) is not str:
                    continue
                yield Token(value=value, line=expr.lineno, col=expr.col_offset)
    return None
