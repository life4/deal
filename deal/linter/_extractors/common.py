# built-in
import ast
from contextlib import suppress
from functools import partial
from pathlib import Path
from types import SimpleNamespace
from typing import Callable, Iterator, List, NamedTuple, Optional, Tuple

# external
import astroid

# app
from .._stub import EXTENSION, StubFile, StubsManager


TOKENS = SimpleNamespace(
    ASSERT=(ast.Assert, astroid.Assert),
    ASSIGN=(ast.Assign, astroid.Assign),
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
    UNARY_OP=(ast.UnaryOp, astroid.UnaryOp),
    WITH=(ast.With, astroid.With),
    YIELD=(ast.Yield, astroid.Yield),
)


class Token(NamedTuple):
    line: int
    col: int
    value: Optional[object] = None
    # marker name or error message:
    marker: Optional[str] = None


def traverse(body: List) -> Iterator:
    for expr in body:
        # breaking apart statements
        if isinstance(expr, TOKENS.EXPR):
            yield expr.value
            yield from _travers_expr(expr=expr.value)
            continue
        if isinstance(expr, TOKENS.IF + TOKENS.FOR):
            yield from traverse(body=expr.body)
            yield from traverse(body=expr.orelse)
            continue

        # breaking apart try-except
        if isinstance(expr, (ast.Try, astroid.TryExcept)):
            for handler in expr.handlers:
                yield from traverse(body=handler.body)
            yield from traverse(body=expr.orelse)
        if isinstance(expr, (ast.Try, astroid.TryFinally)):
            yield from traverse(body=expr.finalbody)
            continue

        # extracting things
        if isinstance(expr, TOKENS.WITH):
            yield from traverse(body=expr.body)
        elif isinstance(expr, TOKENS.RETURN + TOKENS.ASSIGN):
            yield expr.value
        yield expr


def _travers_expr(expr):
    if isinstance(expr, TOKENS.CALL):
        for subnode in expr.args:
            yield from traverse(body=[subnode])
        for subnode in (expr.keywords or ()):
            yield from traverse(body=[subnode.value])


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


def get_full_name(expr) -> Tuple[str, str]:
    if expr.parent is None:
        return '', expr.name

    if type(expr.parent) is astroid.Module:
        return expr.parent.qname(), expr.name

    if type(expr.parent) in (astroid.FunctionDef, astroid.UnboundMethod):
        module_name, func_name = get_full_name(expr=expr.parent)
        return module_name, func_name + '.' + expr.name

    if type(expr.parent) is astroid.ClassDef:
        module_name, class_name = get_full_name(expr=expr.parent)
        return module_name, class_name + '.' + expr.name

    path, _, func_name = expr.qname().rpartition('.')
    return path, func_name


def infer(expr) -> Tuple[astroid.node_classes.NodeNG, ...]:
    if not isinstance(expr, astroid.node_classes.NodeNG):
        return tuple()
    with suppress(astroid.exceptions.InferenceError, RecursionError):
        guesses = expr.infer()
        if guesses is astroid.Uninferable:  # pragma: no cover
            return tuple()
        return tuple(g for g in guesses if type(g) is not astroid.Uninferable)
    return tuple()


def get_stub(
    module_name: Optional[str],
    expr: astroid.FunctionDef,
    stubs: StubsManager,
) -> Optional[StubFile]:
    if not module_name:
        return None
    stub = stubs.get(module_name)
    if stub is not None:
        return stub

    module = _get_module(expr=expr)
    if module is None or module.file is None:
        return None  # pragma: no coverage
    path = Path(module.file).with_suffix(EXTENSION)
    if not path.exists():
        return None
    return stubs.read(path=path)


def _get_module(expr: astroid.node_classes.NodeNG) -> Optional[astroid.Module]:
    if type(expr) is astroid.Module:
        return expr
    if expr.parent is None:
        return None
    return _get_module(expr.parent)


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

    def handle(self, expr, **kwargs):
        handler = self.handlers.get(type(expr))
        if not handler:
            return
        token = handler(expr=expr, **kwargs)
        if token is None:
            return
        if type(token) is Token:
            yield token
            return
        yield from token

    def __call__(self, body: List, **kwargs) -> Iterator[Token]:
        for expr in traverse(body=body):
            yield from self.handle(expr=expr, **kwargs)
