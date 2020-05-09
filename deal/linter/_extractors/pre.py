# built-in
import ast
from typing import Iterator

# external
import astroid

# app
from .common import Extractor, Token, infer
from .contracts import get_contracts
from .value import UNKNOWN, get_value


get_pre = Extractor()


@get_pre.register(astroid.Call)
def handle_call(expr: astroid.Call) -> Iterator[Token]:
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

    for func in infer(expr.func):
        if type(func) is not astroid.FunctionDef:
            continue
        if not func.decorators:
            continue
        code = 'def f({}):0'.format(func.args.as_string())
        func_args = ast.parse(code).body[0].args  # type: ignore

        for category, contract_args in get_contracts(func.decorators.nodes):
            if category != 'pre':
                continue

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
                msg = _format_message(args, kwargs)
                yield Token(value=msg, line=expr.lineno, col=expr.col_offset)


def _format_message(args: list, kwargs: dict) -> str:
    sep = ', '
    args_s = sep.join(map(repr, args))
    kwargs_s = sep.join(['{}={!r}'.format(k, v) for k, v in kwargs.items()])
    if args and kwargs:
        return args_s + sep + kwargs_s
    return args_s + kwargs_s
