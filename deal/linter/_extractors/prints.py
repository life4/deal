# built-in
import ast
from typing import Iterator

# external
import astroid

# app
from .common import TOKENS, Token, get_name, traverse, infer


def get_prints(body: list) -> Iterator[Token]:
    for expr in traverse(body):
        token_info = dict(line=expr.lineno, col=expr.col_offset)
        if isinstance(expr, TOKENS.CALL):
            name = get_name(expr.func)
            if name in ('print', 'sys.stdout', 'sys.stderr'):
                yield Token(value=name, **token_info)
                continue
            if name in ('sys.stdout.write', 'sys.stderr.write'):
                yield Token(value=name[:-6], **token_info)
                continue
            if name == 'open':
                if _is_open_to_write(expr):
                    yield Token(value='open', **token_info)
                continue

        if _is_pathlib_write(expr):
            yield Token(value='Path.open', **token_info)

        if isinstance(expr, TOKENS.WITH):
            for item in expr.items:
                if isinstance(item, ast.withitem):
                    item = item.context_expr
                else:
                    item = item[0]
                if _is_pathlib_write(item):
                    yield Token(value='Path.open', **token_info)
                if not isinstance(item, TOKENS.CALL):
                    continue
                name = get_name(item.func)
                if name == 'open':
                    if _is_open_to_write(item):
                        yield Token(value='open', **token_info)


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
