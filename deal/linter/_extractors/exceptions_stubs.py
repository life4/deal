# built-in
import builtins
from pathlib import Path
from typing import Iterator, Optional

# external
import astroid

# app
from .._contract import Category
from .._stub import EXTENSION, StubFile, StubsManager
from .common import Extractor, Token, infer, get_full_name


get_exceptions_stubs = Extractor()


@get_exceptions_stubs.register(astroid.Call)
def handle_astroid_call(expr: astroid.Call, *, dive: bool = True, stubs: StubsManager) -> Iterator[Token]:
    extra = dict(
        line=expr.lineno,
        col=expr.col_offset,
    )
    for value in infer(expr=expr.func):
        if type(value) is not astroid.FunctionDef:
            continue
        module_name, func_name = get_full_name(expr=value)
        stub = _get_stub(module_name=module_name, expr=value, stubs=stubs)
        if stub is None:
            continue
        names = stub.get(func=func_name, contract=Category.RAISES)
        for name in names:
            name = getattr(builtins, name, name)
            yield Token(value=name, **extra)


def _get_stub(
    module_name: Optional[str], expr: astroid.FunctionDef, stubs: StubsManager,
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


def _get_module(expr) -> Optional[astroid.Module]:
    if type(expr) is astroid.Module:
        return expr
    if expr.parent is None:
        return None
    return _get_module(expr.parent)
