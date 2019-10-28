import ast
import builtins


class Token:
    def __init__(self, value, line: int, col: int):
        self.value = value
        self.line = line
        self.col = col

    @property
    def row(self):
        return self.line - 1


def get_exceptions(body: list = None):
    for expr in body:
        if isinstance(expr, ast.Expr):
            yield from get_exceptions(body=[expr.value])
            continue
        if isinstance(expr, (ast.If, ast.For)):
            yield from get_exceptions(body=expr.body)
            continue

        token_info = dict(line=expr.lineno, col=expr.col_offset)

        # explicit raise
        if isinstance(expr, ast.Raise):
            exc = getattr(builtins, expr.exc.id, expr.exc.id)
            yield Token(value=exc, **token_info)
            continue

        # division by zero
        if isinstance(expr, ast.BinOp) and isinstance(expr.op, ast.Div):
            if isinstance(expr.right, ast.Num) and expr.right.n == 0:
                yield Token(value=ZeroDivisionError, **token_info)
                continue


def get_returns(body: list = None):
    for expr in body:
        if isinstance(expr, ast.Expr):
            yield from get_returns(body=[expr.value])
            continue
        if isinstance(expr, (ast.If, ast.For)):
            yield from get_returns(body=expr.body)
            continue

        token_info = dict(line=expr.lineno, col=expr.col_offset)
        if not isinstance(expr, ast.Return):
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
        if isinstance(expr.value, ast.UnaryOp):
            if isinstance(expr.value.op, ast.USub):
                if isinstance(expr.value.operand, ast.Num):
                    yield Token(
                        value=-expr.value.operand.n,
                        line=expr.lineno,
                        col=expr.col_offset,
                    )
            continue
