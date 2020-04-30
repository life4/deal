# built-in
import ast
from typing import Optional

# external
import astroid

# app
from .common import TOKENS, Extractor, Token, get_name, infer


get_prints = Extractor()


@get_prints.register(*TOKENS.CALL)
def handle_call(expr) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    name = get_name(expr.func)
    if name in ('print', 'sys.stdout', 'sys.stderr'):
        return Token(value=name, **token_info)
    if name in ('sys.stdout.write', 'sys.stderr.write'):
        return Token(value=name[:-6], **token_info)
    if name == 'open':
        if _is_open_to_write(expr):
            return Token(value='open', **token_info)

    if _is_pathlib_write(expr):
        return Token(value='Path.open', **token_info)
    return None


@get_prints.register(*TOKENS.WITH)
def handle_with(expr) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    for item in expr.items:
        if isinstance(item, ast.withitem):
            item = item.context_expr
        else:
            item = item[0]
        if _is_pathlib_write(item):
            return Token(value='Path.open', **token_info)
        if not isinstance(item, TOKENS.CALL):
            continue
        name = get_name(item.func)
        if name == 'open':
            if _is_open_to_write(item):
                return Token(value='open', **token_info)
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
