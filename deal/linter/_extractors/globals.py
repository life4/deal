# built-in
import ast
from typing import Iterator

# external
import astroid

# app
from .common import TOKENS, Token, traverse


def get_globals(body: list) -> Iterator[Token]:
    for expr in traverse(body):
        if isinstance(expr, TOKENS.GLOBAL):
            yield Token(value='global', line=expr.lineno, col=expr.col_offset)
            continue

        if isinstance(expr, TOKENS.NONLOCAL):
            yield Token(value='nonlocal', line=expr.lineno, col=expr.col_offset)
            continue

        if type(expr) is ast.Import:
            yield Token(value='import', line=expr.lineno, col=expr.col_offset)
            continue

        if type(expr) is astroid.Import:
            yield Token(value='import', line=expr.lineno, col=expr.col_offset)
            continue

        if type(expr) is ast.ImportFrom:
            yield Token(value='import', line=expr.lineno, col=expr.col_offset)
            continue

        if type(expr) is astroid.ImportFrom:
            yield Token(value='import', line=expr.lineno, col=expr.col_offset)
            continue
