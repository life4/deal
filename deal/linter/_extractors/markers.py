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
def handle_call(expr, dive: bool = True, stubs: StubsManager = None) -> Iterator[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    name = get_name(expr.func)
    if name is None:
        return

    # stdout and stderr
    token = _check_print(expr=expr, name=name)
    if token is not None:
        yield token
        return
    if name.startswith('sys.stdout.'):
        yield Token(marker='stdout', value='sys.stdout', **token_info)
        return
    if name.startswith('sys.stderr.'):
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

    yield from _infer_markers(expr=expr, dive=dive, stubs=stubs)


def _infer_markers(expr, dive: bool, stubs: StubsManager = None) -> Iterator[Token]:
    inferred = infer(expr=expr.func)
    stubs_found = False
    if type(expr) is astroid.Call and stubs is not None:
        for token in _markers_from_stubs(expr=expr, inferred=inferred, stubs=stubs):
            stubs_found = True
            yield token

    # Infer function call and check the function body for raises.
    # Do not dive into called function if we already found stubs for it.
    if not stubs_found and dive:
        yield from _markers_from_func(expr=expr, inferred=inferred)


@get_markers.register(*TOKENS.WITH)
def handle_with(expr, **kwargs) -> Optional[Token]:
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


def _markers_from_stubs(expr: astroid.Call, inferred, stubs: StubsManager) -> Iterator[Token]:
    for value in inferred:
        if type(value) is not astroid.FunctionDef:
            continue
        module_name, func_name = get_full_name(expr=value)
        stub = get_stub(module_name=module_name, expr=value, stubs=stubs)
        if stub is None:
            continue
        names = stub.get(func=func_name, contract=Category.HAS)
        for name in names:
            yield Token(marker=name, line=expr.lineno, col=expr.col_offset)


def _markers_from_func(expr, inferred) -> Iterator[Token]:
    for value in inferred:
        if type(value) is not astroid.FunctionDef:
            continue

        # recursively infer markers from the function body
        for token in get_markers(body=value.body, dive=False):
            yield Token(
                marker=token.marker,
                value=token.value,
                line=expr.lineno,
                col=expr.col_offset,
            )

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
                yield Token(marker=value, line=expr.lineno, col=expr.col_offset)
    return None


def _check_print(expr, name: str) -> Optional[Token]:
    """Return token if expr is `print` function call.

    Marker type depends on `file=` keyword argument.
    If it is missed, the type is `stdout`.
    If it is `stdout` or `stderr`, the type is `stdout` or `stderr`.
    Otherwise, there is no marker. It writes something into a stream, and it's ok.
    """
    if name != 'print':
        return None
    for kwarg in (expr.keywords or []):
        if kwarg.arg != 'file':
            continue
        value = get_name(expr=kwarg.value)
        if value in ('stdout', 'sys.stdout'):
            return Token(
                marker='stdout',
                value='print',
                line=expr.lineno,
                col=expr.col_offset,
            )
        if value in ('stderr', 'sys.stderr'):
            return Token(
                marker='stderr',
                value='print',
                line=expr.lineno,
                col=expr.col_offset,
            )
        return None
    return Token(
        marker='stdout',
        value='print',
        line=expr.lineno,
        col=expr.col_offset,
    )
