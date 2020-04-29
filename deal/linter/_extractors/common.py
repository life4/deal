# built-in
import ast
from contextlib import suppress
from types import SimpleNamespace
from typing import Iterator, List, NamedTuple, Optional, Union

# external
import astroid


AstroidNode = astroid.node_classes.NodeNG
Node = Union[ast.AST, AstroidNode]

TOKENS = SimpleNamespace(
    ASSERT=(ast.Assert, astroid.Assert),
    ATTR=(ast.Attribute, astroid.Attribute),
    BIN_OP=(ast.BinOp, astroid.BinOp),
    CALL=(ast.Call, astroid.Call),
    EXPR=(ast.Expr, astroid.Expr),
    FOR=(ast.For, astroid.For),
    FUNC=(ast.FunctionDef, astroid.FunctionDef),
    GLOBAL=(ast.Global, astroid.Global),
    IF=(ast.If, astroid.If),
    NAME=(ast.Name, astroid.Name),
    NONLOCAL=(ast.Nonlocal, astroid.Nonlocal),
    RAISE=(ast.Raise, astroid.Raise),
    RETURN=(ast.Return, astroid.Return),
    TRY=(ast.Try, astroid.TryExcept, astroid.TryFinally),
    UNARY_OP=(ast.UnaryOp, astroid.UnaryOp),
    WITH=(ast.With, astroid.With),
)


class Token(NamedTuple):
    value: object
    line: int
    col: int


def traverse(body: List[Node]) -> Iterator[Node]:
    for expr in body:
        # breaking apart
        if isinstance(expr, TOKENS.EXPR):
            yield expr.value
            continue
        if isinstance(expr, TOKENS.IF + TOKENS.FOR):
            yield from traverse(body=expr.body)
            yield from traverse(body=expr.orelse)
            continue
        if isinstance(expr, TOKENS.TRY):
            if hasattr(expr, 'orelse'):
                yield from traverse(body=expr.orelse)
            if hasattr(expr, 'finalbody'):
                yield from traverse(body=expr.finalbody)
            continue

        # extracting things
        if isinstance(expr, TOKENS.WITH):
            yield from traverse(body=expr.body)
        if isinstance(expr, TOKENS.RETURN):
            yield expr.value
        yield expr


def get_name(expr) -> Optional[str]:
    if isinstance(expr, ast.Name):
        return expr.id
    if isinstance(expr, astroid.Name):
        return expr.name

    if isinstance(expr, astroid.Attribute):
        left = get_name(expr.expr)
        if left is None:
            return None
        return left + '.' + expr.attrname
    if isinstance(expr, ast.Attribute):
        left = get_name(expr.value)
        if left is None:
            return None
        return left + '.' + expr.attr

    return None


def infer(expr: astroid.node_classes.NodeNG) -> tuple:
    with suppress(astroid.exceptions.InferenceError, RecursionError):
        return tuple(expr.infer())
    return tuple()
