# built-in
import ast
from typing import Iterator

# external
import astroid

# app
from .common import Extractor, Token, infer
from .contracts import get_contracts
from .value import get_value, UNKNOWN


get_pre = Extractor()


@get_pre.register(astroid.Call)
def handle_call(expr: astroid.Call, dive: bool = True) -> Iterator[Token]:
    from .._contract import Contract, Category

    args = []
    for subnode in expr.args:
        value = get_value(expr=subnode)
        if value is UNKNOWN:
            return
        args.append(value)

    kwargs = {}
    for subnode in (expr.keywords or ()):
        value = get_value(expr=subnode.value)
        if value is UNKNOWN:
            return
        kwargs[subnode.arg] = value

    code = 'def f({}):0'.format(expr.args.as_string())
    func_args = ast.parse(code).body[0].args  # type: ignore

    for contract_args in _get_pre_contracts(expr=expr):
        contract = Contract(
            args=contract_args,
            category=Category.PRE,
            func_args=func_args,
        )
        try:
            result = contract.run(*args, **kwargs)
        except NameError:
            continue
        if result is False or type(result) is str:
            yield Token(value=(args, kwargs), line=expr.lineno, col=expr.col_offset)


def _get_pre_contracts(expr: astroid.Call):
    for value in infer(expr.func):
        if type(value) is not astroid.FunctionDef:
            continue
        if not value.decorators:
            continue
        for category, args in get_contracts(value.decorators.nodes):
            if category != 'pre':
                continue
            yield args
