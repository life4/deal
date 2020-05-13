# built-in
import builtins
from typing import Iterator

# external
import astroid

# app
from .._contract import Category
from .._stub import StubsManager
from .common import Extractor, Token, infer, get_full_name, get_stub


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
        stub = get_stub(module_name=module_name, expr=value, stubs=stubs)
        if stub is None:
            continue
        names = stub.get(func=func_name, contract=Category.RAISES)
        for name in names:
            name = getattr(builtins, name, name)
            yield Token(value=name, **extra)
