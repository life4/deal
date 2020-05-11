import ast
from typing import Optional

# external
import astroid

# app
from .common import TOKENS, Extractor, Token, get_name, infer


get_markers = Extractor()


@get_markers.register(*TOKENS.GLOBAL)
def handle_global(expr) -> Optional[Token]:
    return Token(marker='global', line=expr.lineno, col=expr.col_offset)


@get_markers.register(*TOKENS.NONLOCAL)
def handle_nonlocal(expr) -> Optional[Token]:
    return Token(marker='global', line=expr.lineno, col=expr.col_offset)


@get_markers.register(ast.Import)
def handle_ast_import(expr: ast.Import) -> Optional[Token]:
    return Token(marker='import', line=expr.lineno, col=expr.col_offset)


@get_markers.register(astroid.Import)
def handle_astroid_import(expr: astroid.Import) -> Optional[Token]:
    return Token(marker='import', line=expr.lineno, col=expr.col_offset)


@get_markers.register(ast.ImportFrom)
def handle_ast_import_from(expr: ast.ImportFrom) -> Optional[Token]:
    return Token(marker='import', line=expr.lineno, col=expr.col_offset)


@get_markers.register(astroid.ImportFrom)
def handle_astroid_import_from(expr: astroid.ImportFrom) -> Optional[Token]:
    return Token(marker='import', line=expr.lineno, col=expr.col_offset)


@get_markers.register(*TOKENS.CALL)
def handle_call(expr) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    name = get_name(expr.func)

    # stdout and stderr
    if name == 'print':
        return Token(marker='stdout', value='print', **token_info)
    if name in ('print', 'sys.stdout', 'sys.stdout.write'):
        return Token(marker='stdout', value='sys.stdout', **token_info)
    if name in ('sys.stderr', 'sys.stderr.write'):
        return Token(marker='stderr', value='sys.stderr', **token_info)

    # read and write
    if name == 'open':
        if _is_open_to_write(expr):
            return Token(marker='write', value='open', **token_info)
        return Token(marker='read', value='open', **token_info)
    if _is_pathlib_write(expr):
        return Token(marker='write', value='Path.open', **token_info)

    return None


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
