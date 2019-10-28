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
        if not isinstance(expr, ast.Raise):
            continue
        exc = getattr(builtins, expr.exc.id, None)
        if exc is None:
            continue
        yield Token(value=exc, line=expr.lineno, col=expr.col_offset)


def get_returns(body: list = None):
    for expr in body:
        if not isinstance(expr, ast.Return):
            continue

        # string
        if isinstance(expr.value, ast.Str):
            yield Token(value=expr.value.s, line=expr.lineno, col=expr.col_offset)
            continue

        # positive number
        if isinstance(expr.value, ast.Num):
            yield Token(value=expr.value.n, line=expr.lineno, col=expr.col_offset)
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
