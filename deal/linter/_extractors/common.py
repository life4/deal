# built-in
import ast
from contextlib import suppress
from functools import partial
from types import SimpleNamespace
from typing import Callable, Iterator, List, NamedTuple, Optional, Tuple

# external
import astroid


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


def traverse(body: List) -> Iterator:
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


def infer(expr) -> Tuple:
    with suppress(astroid.exceptions.InferenceError, RecursionError):
        return tuple(g for g in expr.infer() if type(g) is not astroid.Uninferable)
    return tuple()


class Extractor:
    __slots__ = ('handlers', )

    def __init__(self):
        self.handlers = dict()

    def _register(self, types: Tuple[type], handler: Callable) -> Callable:
        for tp in types:
            # it's here to have `getattr` to get nodes from `ast` module
            # that are available only in some Python versions.
            if tp is None:
                continue  # pragma: no coverage
            self.handlers[tp] = handler
        return handler

    def register(self, *types):
        return partial(self._register, types)

    def __call__(self, body: List, **kwargs) -> Iterator[Token]:
        for expr in traverse(body=body):
            handler = self.handlers.get(type(expr))
            if not handler:
                continue
            token = handler(expr=expr, **kwargs)
            if token is None:
                continue
            if type(token) is Token:
                yield token
                continue
            yield from token
