# built-in
import ast
from typing import Optional

# external
import astroid

# app
from .common import TOKENS, Extractor, Token, infer


get_asserts = Extractor()
inner_extractor = Extractor()


@get_asserts.register(*TOKENS.ASSERT)
def handle_assert(expr) -> Optional[Token]:
    # inner_extractor
    for token in inner_extractor.handle(expr=expr.test):
        return token

    # astroid inference
    if hasattr(expr.test, 'infer'):
        for value in infer(expr.test):
            if not isinstance(value, astroid.Const):
                continue
            if value.value:
                continue
            return Token(value=value.value, line=expr.lineno, col=expr.col_offset)
    return None


# any constant value in astroid
@inner_extractor.register(astroid.Const)
def handle_const(expr: astroid.Const) -> Optional[Token]:
    if expr.value:
        return None
    return Token(value=expr.value, line=expr.lineno, col=expr.col_offset)


# Python <3.8
# string, binary string
@inner_extractor.register(ast.Str, ast.Bytes)
def handle_str(expr) -> Optional[Token]:
    if expr.s:
        return None
    return Token(value=expr.s, line=expr.lineno, col=expr.col_offset)


# Python <3.8
# True, False, None
@inner_extractor.register(ast.NameConstant)
def handle_name_constant(expr: ast.NameConstant) -> Optional[Token]:
    if expr.value:
        return None
    return Token(value=expr.value, line=expr.lineno, col=expr.col_offset)


# positive number
@inner_extractor.register(ast.Num, getattr(ast, 'Constant', None))
def handle_num(expr) -> Optional[Token]:
    if expr.n:
        return None
    return Token(value=expr.n, line=expr.lineno, col=expr.col_offset)
