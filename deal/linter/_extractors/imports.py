# built-in
import ast

# external
import astroid

# app
from .common import Extractor, Token


get_imports = Extractor()


@get_imports.register(astroid.ImportFrom)
def handle_astroid(expr: astroid.ImportFrom) -> Token:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    dots = '.' * (expr.level or 0)
    name = expr.modname or ''
    return Token(value=dots + name, **token_info)


@get_imports.register(ast.ImportFrom)
def handle_ast(expr: ast.ImportFrom) -> Token:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    dots = '.' * expr.level
    name = expr.module or ''
    return Token(value=dots + name, **token_info)
