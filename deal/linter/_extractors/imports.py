import ast
from typing import Iterator

import astroid

from .common import traverse, Token


def get_imports(body: list) -> Iterator[Token]:
    for expr in traverse(body):
        token_info = dict(line=expr.lineno, col=expr.col_offset)
        if isinstance(expr, astroid.ImportFrom):
            yield Token(value=expr.modname, **token_info)
        if isinstance(expr, ast.ImportFrom):
            yield Token(value=expr.module, **token_info)
