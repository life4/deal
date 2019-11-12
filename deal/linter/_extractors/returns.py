import ast
from typing import Iterator

import astroid

from .common import traverse, Token, TOKENS


def get_returns(body: list) -> Iterator[Token]:
    for expr in traverse(body):
        if not isinstance(expr, TOKENS.RETURN):
            continue
        token_info = dict(line=expr.lineno, col=expr.value.col_offset)

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

        # astroid inference
        if hasattr(expr.value, 'infer'):
            try:
                guesses = tuple(expr.value.infer())
            except astroid.exceptions.NameInferenceError:
                continue
            for value in guesses:
                if isinstance(value, astroid.Const):
                    yield Token(value=value.value, **token_info)
