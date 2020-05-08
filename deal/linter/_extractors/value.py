# built-in
import ast
from typing import Union

# external
import astroid

# app
from .common import Extractor, infer


inner_extractor = Extractor()
UNKNOWN = object()


def get_value(expr):
    handler = inner_extractor.handlers.get(type(expr))
    if handler:
        value = handler(expr=expr)
        if value is not UNKNOWN:
            return value

    # astroid inference
    if hasattr(expr, 'infer'):
        for parent_expr in infer(expr=expr):
            value = get_value(expr=parent_expr)
            if value is not UNKNOWN:
                return value
    return UNKNOWN


# any constant value in astroid
@inner_extractor.register(astroid.Const)
def handle_const(expr: astroid.Const):
    return expr.value


# Python <3.8
# string, binary string
@inner_extractor.register(ast.Str, ast.Bytes)
def handle_str(expr) -> Union[str, bytes]:  # pragma: py>=38
    return expr.s


# Python <3.8
# True, False, None
@inner_extractor.register(ast.NameConstant)
def handle_name_constant(expr: ast.NameConstant):  # pragma: py>=38
    return expr.value


# positive number
@inner_extractor.register(ast.Num, getattr(ast, 'Constant', None))
def handle_num(expr) -> float:
    return expr.n


# negative number
# No need to handle astroid here, it can be inferred later.
@inner_extractor.register(ast.UnaryOp)
def handle_unary_op(expr: ast.UnaryOp):
    # in Python 3.8 it is ast.Constant but it is subclass of ast.Num.
    if not isinstance(expr.operand, ast.Num):
        return UNKNOWN

    value = expr.operand.n
    is_minus = type(expr.op) is ast.USub or expr.op == '-'
    is_plus = type(expr.op) is ast.UAdd or expr.op == '+'
    if is_minus:
        value = -value
    if is_minus or is_plus:
        return value
    return UNKNOWN
