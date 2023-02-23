from __future__ import annotations

import ast
from collections import deque
from contextlib import suppress
from functools import partial
from pathlib import Path
from typing import Callable, Iterator, NamedTuple, Tuple, Type, TypeVar

from .._stub import EXTENSION, StubFile, StubsManager


try:
    import astroid
except ImportError:
    astroid = None


T = TypeVar('T')
N = Tuple[Type[T], Type[T]]
Handler = Callable[..., 'Token | Iterator[Token] | None']


def _get_type(name: str) -> tuple[type, type]:
    ast_type = getattr(ast, name)
    if astroid is not None:
        astroid_type = getattr(astroid, name)
        return (ast_type, astroid_type)
    return (ast_type, ast_type)


class TOKENS:
    ASSERT: N[ast.Assert] = _get_type('Assert')
    ATTR: N[ast.Attribute] = _get_type('Attribute')
    BIN_OP: N[ast.BinOp] = _get_type('BinOp')
    CALL: N[ast.Call] = _get_type('Call')
    COMPARE: N[ast.Compare] = _get_type('Compare')
    GLOBAL: N[ast.Global] = _get_type('Global')
    LAMBDA: N[ast.Lambda] = _get_type('Lambda')
    NONLOCAL: N[ast.Nonlocal] = _get_type('Nonlocal')
    RAISE: N[ast.Raise] = _get_type('Raise')
    RETURN: N[ast.Return] = _get_type('Return')
    YIELD_FROM: N[ast.YieldFrom] = _get_type('YieldFrom')
    YIELD: N[ast.Yield] = _get_type('Yield')


DEFAULT_LINE = 0
DEFAULT_COL = 1


class Token(NamedTuple):
    line: int = DEFAULT_LINE
    col: int = DEFAULT_COL
    value: object | None = None
    marker: str | None = None  # marker name or error message


def traverse(body: list[ast.AST | astroid.NodeNG]) -> Iterator[ast.AST | astroid.NodeNG]:
    for expr in body:
        if isinstance(expr, ast.AST):
            yield from _traverse_ast(expr)
        else:
            yield from _traverse_astroid(expr)


def _traverse_ast(node: ast.AST) -> Iterator[ast.AST]:
    todo = deque([node])
    while todo:
        node = todo.popleft()
        if isinstance(node, ast.Try):
            for h in node.handlers:
                todo.extend(h.body)
            todo.extend(node.orelse)
            todo.extend(node.finalbody)
        else:
            todo.extend(ast.iter_child_nodes(node))
            yield node


def _traverse_astroid(node: astroid.NodeNG) -> Iterator[astroid.NodeNG]:
    todo: deque[astroid.NodeNG] = deque([node])
    while todo:
        node = todo.popleft()
        if isinstance(node, astroid.TryExcept):
            for h in node.handlers:
                todo.extend(h.body)
            todo.extend(node.orelse)
        else:
            todo.extend(node.get_children())
            yield node


def get_name(expr: ast.AST | astroid.NodeNG) -> str | None:
    if isinstance(expr, ast.Name):
        return expr.id
    if astroid is not None and isinstance(expr, astroid.Name):
        return expr.name

    if astroid is not None and isinstance(expr, astroid.Attribute):
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


def get_full_name(
    expr: astroid.Module | astroid.FunctionDef | astroid.UnboundMethod | astroid.ClassDef,
) -> Tuple[str, str]:
    if expr.parent is None:
        return '', expr.name

    if isinstance(expr.parent, astroid.Module):
        return expr.parent.qname(), expr.name

    if isinstance(expr.parent, (astroid.FunctionDef, astroid.UnboundMethod)):
        module_name, func_name = get_full_name(expr=expr.parent)
        return module_name, func_name + '.' + expr.name

    if isinstance(expr.parent, astroid.ClassDef):
        module_name, class_name = get_full_name(expr=expr.parent)
        return module_name, class_name + '.' + expr.name

    path, _, func_name = expr.qname().rpartition('.')
    return path, func_name


def infer(expr: ast.AST | astroid.NodeNG) -> Tuple[astroid.NodeNG, ...]:
    if isinstance(expr, ast.AST):
        return tuple()
    with suppress(astroid.InferenceError, RecursionError):
        guesses = expr.infer()
        if guesses is astroid.Uninferable:  # pragma: no cover
            return tuple()
        return tuple(g for g in guesses if repr(g) != 'Uninferable')
    return tuple()


def get_stub(
    module_name: str | None,
    expr: astroid.FunctionDef,
    stubs: StubsManager,
) -> StubFile | None:
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


def _get_module(expr: astroid.NodeNG) -> astroid.Module | None:
    if isinstance(expr, astroid.Module):
        return expr
    if expr.parent is None:
        return None
    return _get_module(expr.parent)


class Extractor:
    __slots__ = ('handlers', )
    handlers: dict[type, Handler]

    def __init__(self) -> None:
        self.handlers = dict()

    def register(
        self, *types: type | Callable[[], type],
    ) -> Callable[[Handler], Handler]:
        types = tuple(self._eval_types(types))
        return partial(self._register, types)

    @staticmethod
    def _eval_types(types: tuple[type | Callable[[], type], ...]) -> Iterator[type]:
        for t in types:
            if isinstance(t, type):
                yield t
                continue
            try:
                yield t()
            except (NameError, AttributeError):
                pass

    def _register(self, types: Tuple[type], handler: Handler) -> Handler:
        for tp in types:
            # it's here to have `getattr` to get nodes from `ast` module
            # that are available only in some Python versions.
            if tp is None:
                continue  # pragma: no coverage
            self.handlers[tp] = handler
        return handler

    def __call__(self, body: list, **kwargs) -> Iterator[Token]:
        for expr in traverse(body=body):
            for token in self._handle(expr=expr, **kwargs):
                yield self._ensure_node_info(expr=expr, token=token)

    def _handle(self, expr: ast.AST | astroid.NodeNG, **kwargs) -> Iterator[Token]:
        handler = self.handlers.get(type(expr))
        if handler is None:
            return
        token = handler(expr=expr, **kwargs)
        if token is None:
            return
        if isinstance(token, Token):
            yield token
            return
        yield from token

    @staticmethod
    def _ensure_node_info(token: Token, expr: ast.AST | astroid.NodeNG) -> Token:
        if token.line == DEFAULT_LINE:
            token = token._replace(line=expr.lineno)
        if token.col == DEFAULT_COL:
            token = token._replace(col=expr.col_offset)
        return token
