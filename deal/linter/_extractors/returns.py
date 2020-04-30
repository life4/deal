# built-in
import ast
from typing import Optional

# external
import astroid

# app
from .common import TOKENS, Token, Extractor, infer


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
                token_info = dict(line=expr.lineno, col=expr.col_offset)
                return Token(value=value.value, **token_info)
    return None


# any constant value in astroid
@inner_extractor.register(astroid.Const)
def handle_const(expr) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    return Token(value=expr.value, **token_info)


# string, binary string
@inner_extractor.register(ast.Str, ast.Bytes)
def handle_str(expr) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    return Token(value=expr.s, **token_info)


# True, False, None
@inner_extractor.register(ast.NameConstant)
def handle_name_constant(expr) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    return Token(value=expr.value, **token_info)


# positive number
@inner_extractor.register(ast.Num, getattr(ast, 'Constant', None))
def handle_num(expr) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    return Token(value=expr.n, **token_info)


# negative number
@inner_extractor.register(*TOKENS.UNARY_OP)
def handle_unary_op(expr) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    is_minus = isinstance(expr.op, ast.USub) or expr.op == '-'
    if is_minus:
        if isinstance(expr.operand, ast.Num):
            return Token(value=-expr.operand.n, **token_info)
        if isinstance(expr.operand, astroid.Const):
            return Token(value=-expr.operand.value, **token_info)
