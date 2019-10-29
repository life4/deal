import ast
import builtins
from types import SimpleNamespace

import astroid


TOKENS = SimpleNamespace(
    BIN_OP=(ast.BinOp, astroid.BinOp),
    CALL=(ast.Call, astroid.Call),
    EXPR=(ast.Expr, astroid.Expr),
    FOR=(ast.For, astroid.For),
    IF=(ast.If, astroid.If),
    RAISE=(ast.Raise, astroid.Raise),
    RETURN=(ast.Return, astroid.Return),
    TRY=(ast.Try, astroid.TryExcept, astroid.TryFinally),
    UNARY_OP=(ast.UnaryOp, astroid.UnaryOp),
    WITH=(ast.With, astroid.With),
)


class Token:
    def __init__(self, value, line: int, col: int):
        self.value = value
        self.line = line
        self.col = col

    @property
    def row(self):
        return self.line - 1


def _traverse(body):
    for expr in body:
        if isinstance(expr, TOKENS.EXPR):
            yield expr.value
            continue
        if isinstance(expr, TOKENS.IF + TOKENS.FOR):
            yield from _traverse(body=expr.body)
            yield from _traverse(body=expr.orelse)
            continue
        if isinstance(expr, TOKENS.TRY):
            if hasattr(expr, 'orelse'):
                yield from _traverse(body=expr.orelse)
            if hasattr(expr, 'finalbody'):
                yield from _traverse(body=expr.finalbody)
            continue
        if isinstance(expr, TOKENS.WITH):
            yield from _traverse(body=expr.body)
            continue
        yield expr


def _get_name(expr):
    if isinstance(expr, ast.Name):
        return expr.id
    if isinstance(expr, astroid.Name):
        return expr.name
    return None


def get_exceptions(body: list = None):
    for expr in _traverse(body):
        token_info = dict(line=expr.lineno, col=expr.col_offset)

        # explicit raise
        if isinstance(expr, TOKENS.RAISE):
            name = _get_name(expr.exc)
            if not name:
                continue
            exc = getattr(builtins, name, name)
            yield Token(value=exc, **token_info)
            continue

        # division by zero
        if isinstance(expr, TOKENS.BIN_OP):
            if isinstance(expr.op, ast.Div) or expr.op == '/':
                if isinstance(expr.right, astroid.Const) and expr.right.value == 0:
                    yield Token(value=ZeroDivisionError, **token_info)
                    continue
                if isinstance(expr.right, ast.Num) and expr.right.n == 0:
                    yield Token(value=ZeroDivisionError, **token_info)
                    continue

        if isinstance(expr, TOKENS.CALL):
            name = _get_name(expr.func)
            if name and name == 'exit':
                yield Token(value=SystemExit, **token_info)
                continue


def get_returns(body: list = None):
    for expr in _traverse(body):
        token_info = dict(line=expr.lineno, col=expr.col_offset)
        if not isinstance(expr, TOKENS.RETURN):
            continue

        # any constant value in astroid
        if isinstance(expr.value, astroid.Const):
            yield Token(value=expr.value.value, **token_info)
            continue

        # string, binary string
        if isinstance(expr.value, (ast.Str, ast.Bytes)):
            yield Token(value=expr.value.s, **token_info)
            continue

        # True, False, None
        if isinstance(expr.value, ast.NameConstant):
            yield Token(value=expr.value.value, **token_info)
            continue

        # positive number
        if isinstance(expr.value, ast.Num):
            yield Token(value=expr.value.n, **token_info)
            continue

        # negative number
        if isinstance(expr.value, TOKENS.UNARY_OP):
            is_minus = isinstance(expr.value.op, ast.USub) or expr.value.op == '-'
            if is_minus:
                if isinstance(expr.value.operand, ast.Num):
                    yield Token(value=-expr.value.operand.n, **token_info)
                    continue
                if isinstance(expr.value.operand, astroid.Const):
                    yield Token(value=-expr.value.operand.value, **token_info)
                    continue
