# built-in
import ast
from typing import Optional

# external
import astroid

# app
from .common import TOKENS, Extractor, Token


get_globals = Extractor()


@get_globals.register(*TOKENS.GLOBAL)
def handle_global(expr) -> Optional[Token]:
    return Token(value='global', line=expr.lineno, col=expr.col_offset)


@get_globals.register(*TOKENS.NONLOCAL)
def handle_nonlocal(expr) -> Optional[Token]:
    return Token(value='nonlocal', line=expr.lineno, col=expr.col_offset)


@get_globals.register(ast.Import)
def handle_ast_import(expr: ast.Import) -> Optional[Token]:
    return Token(value='import', line=expr.lineno, col=expr.col_offset)


@get_globals.register(astroid.Import)
def handle_astroid_import(expr: astroid.Import) -> Optional[Token]:
    return Token(value='import', line=expr.lineno, col=expr.col_offset)


@get_globals.register(ast.ImportFrom)
def handle_ast_import_from(expr: ast.ImportFrom) -> Optional[Token]:
    return Token(value='import', line=expr.lineno, col=expr.col_offset)


@get_globals.register(astroid.ImportFrom)
def handle_astroid_import_from(expr: astroid.ImportFrom) -> Optional[Token]:
    return Token(value='import', line=expr.lineno, col=expr.col_offset)
