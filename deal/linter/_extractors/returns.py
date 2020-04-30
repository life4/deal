# built-in
import ast
from typing import Optional

# external
import astroid

# app
from .common import TOKENS, Extractor, Token, infer


get_returns = Extractor()
inner_extractor = Extractor()


@get_returns.register(*TOKENS.RETURN)
def handle_returns(expr) -> Optional[Token]:
    handler = inner_extractor.handlers.get(type(expr.value))
    if handler:
        token = handler(expr=expr.value)
        if token is not None:
            return token

    # astroid inference
    if hasattr(expr.value, 'infer'):
        for value in infer(expr.value):
            if isinstance(value, astroid.Const):
                token_info = dict(line=expr.lineno, col=expr.value.col_offset)
                return Token(value=value.value, **token_info)
    return None


# any constant value in astroid
@inner_extractor.register(astroid.Const)
def handle_const(expr: astroid.Const) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    return Token(value=expr.value, **token_info)


# Python <3.8
# string, binary string
@inner_extractor.register(ast.Str, ast.Bytes)
def handle_str(expr) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    return Token(value=expr.s, **token_info)


# Python <3.8
# True, False, None
@inner_extractor.register(ast.NameConstant)
def handle_name_constant(expr: ast.NameConstant) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    return Token(value=expr.value, **token_info)


# positive number
@inner_extractor.register(ast.Num, getattr(ast, 'Constant', None))
def handle_num(expr) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    return Token(value=expr.n, **token_info)


# negative number
# No need to handle astroid here, it can be inferred later.
@inner_extractor.register(ast.UnaryOp)
def handle_unary_op(expr: ast.UnaryOp) -> Optional[Token]:
    # in Python 3.8 it is ast.Constant but it is subclass of ast.Num.
    if not isinstance(expr.operand, ast.Num):
        return

    token_info = dict(line=expr.lineno, col=expr.col_offset)
    value = expr.operand.n
    is_minus = type(expr.op) is ast.USub or expr.op == '-'
    is_plus = type(expr.op) is ast.UAdd or expr.op == '+'
    if is_minus:
        value = -value
    if is_minus or is_plus:
        return Token(value=value, **token_info)
    return None
