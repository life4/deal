import ast
from typing import Iterator

import astroid

from .common import traverse, Token


def get_imports(body: list) -> Iterator[Token]:
    for expr in traverse(body):
        token_info = dict(line=expr.lineno, col=expr.col_offset)
        if isinstance(expr, astroid.ImportFrom):
            dots = '.' * (expr.level or 0)
            yield Token(value=dots + expr.modname, **token_info)
        if isinstance(expr, ast.ImportFrom):
            dots = '.' * expr.level
            yield Token(value=dots + expr.module, **token_info)
