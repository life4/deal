import ast

import astroid

from .common import Extractor, Token


get_imports = Extractor()


@get_imports.register(astroid.ImportFrom)
def handle_astroid(expr: astroid.ImportFrom) -> Token:
    dots = '.' * (expr.level or 0)
    name = expr.modname or ''
    return Token(value=dots + name, line=expr.lineno, col=expr.col_offset)


@get_imports.register(ast.ImportFrom)
def handle_ast(expr: ast.ImportFrom) -> Token:
    dots = '.' * expr.level
    name = expr.module or ''
    return Token(value=dots + name, line=expr.lineno, col=expr.col_offset)
