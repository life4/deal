# built-in
import builtins
from pathlib import Path
from typing import Iterator, List, Optional, Tuple

# external
import astroid

# app
from .._contract import Category
from .._stub import EXTENSION, StubFile, StubsManager
from .common import AstroidNode, Node, Token, infer, traverse


def get_exceptions_stubs(body: List[Node], *, dive: bool = True, stubs: StubsManager) -> Iterator[Token]:
    for expr in traverse(body):
        if type(expr) is not astroid.Call:
            return
        extra = dict(
            line=expr.lineno,
            col=expr.col_offset,
        )
        for value in infer(expr=expr.func):
            if type(value) is not astroid.FunctionDef:
                continue
            module_name, func_name = _get_full_name(expr=value)
            stub = _get_stub(module_name=module_name, expr=value, stubs=stubs)
            if stub is None:
                continue
            names = stub.get(func=func_name, contract=Category.RAISES)
            for name in names:
                name = getattr(builtins, name, name)
                yield Token(value=name, **extra)


def _get_stub(module_name: Optional[str], expr: astroid.FunctionDef, stubs: StubsManager) -> StubFile:
    if not module_name:
        return None
    stub = stubs.get(module_name)
    if stub is not None:
        return stub

    module = _get_module(expr=expr)
    if module.file is None:
        return None
    path = Path(module.file).with_suffix(EXTENSION)
    if not path.exists():
        return None
    return stubs.read(path=path)


def _get_module(expr: AstroidNode) -> Optional[astroid.Module]:
    if type(expr) is astroid.Module:
        return expr
    if expr.parent is None:
        return None
    return _get_module(expr.parent)


def _get_full_name(expr: AstroidNode) -> Tuple[str, str]:
    if expr.parent is None:
        return '', expr.name  # pragma: no cover

    if type(expr.parent) is astroid.Module:
        return expr.parent.qname(), expr.name

    if type(expr.parent) is astroid.FunctionDef:
        module_name, func_name = _get_full_name(expr=expr.parent)
        return module_name, func_name + '.' + expr.name

    if type(expr.parent) is astroid.ClassDef:
        module_name, class_name = _get_full_name(expr=expr.parent)
        return module_name, class_name + '.' + expr.name

    path, _, func_name = expr.qname().rpartition('.')
    return path, func_name
