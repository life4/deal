import ast
from typing import Iterator

import astroid

from .common import traverse, Token


def get_imports(body: list) -> Iterator[Token]:
    for expr in traverse(body):
        token_info = dict(line=expr.lineno, col=expr.col_offset)
        if isinstance(expr, astroid.ImportFrom):
            dots = '.' * (expr.level or 0)
            name = expr.modname or ''
            yield Token(value=dots + name, **token_info)
        if isinstance(expr, ast.ImportFrom):
            dots = '.' * expr.level
            name = expr.module or ''
            yield Token(value=dots + name, **token_info)
