import ast
from typing import Iterator, List, NamedTuple, Optional, Union

import astroid

from .common import TOKENS, get_name


SUPPORTED_CONTRACTS = frozenset({
    'deal.ensure',
    'deal.example',
    'deal.has',
    'deal.post',
    'deal.pre',
    'deal.pure',
    'deal.raises',
    'deal.safe',
})
SUPPORTED_MARKERS = frozenset({'deal.pure', 'deal.safe', 'deal.inherit'})
Attr = Union[ast.Attribute, astroid.Attribute]


class ContractInfo(NamedTuple):
    name: str
    args: List[Union[ast.expr, astroid.Expr]]
    line: int


def get_contracts(func) -> Iterator[ContractInfo]:
    if isinstance(func, ast.FunctionDef):
        yield from _get_contracts(func.decorator_list)
        return

    assert isinstance(func, (astroid.FunctionDef, astroid.UnboundMethod))
    if func.decorators is None:
        return
    assert isinstance(func.decorators, astroid.Decorators)
    yield from _get_contracts(func.decorators.nodes)


def _get_contracts(decorators: list) -> Iterator[ContractInfo]:
    for contract in decorators:
        if isinstance(contract, TOKENS.ATTR):
            name = get_name(contract)
            if name not in SUPPORTED_MARKERS:
                continue
            yield ContractInfo(
                name=name.split('.')[-1],
                args=[],
                line=contract.lineno,
            )
            if name == 'deal.inherit':
                yield from _resolve_inherit(contract)

        if isinstance(contract, TOKENS.CALL):
            if not isinstance(contract.func, TOKENS.ATTR):
                continue
            name = get_name(contract.func)
            if name == 'deal.chain':
                yield from _get_contracts(contract.args)
            if name not in SUPPORTED_CONTRACTS:
                continue
            yield ContractInfo(
                name=name.split('.')[-1],
                args=contract.args,
                line=contract.lineno,
            )

        # infer assigned value
        if isinstance(contract, astroid.Name):
            assigments = contract.lookup(contract.name)[1]
            if not assigments:
                continue
            # use only the closest assignment
            expr = assigments[0]
            # can it be not an assignment? IDK
            if not isinstance(expr, astroid.AssignName):  # pragma: no cover
                continue
            expr = expr.parent
            if not isinstance(expr, astroid.Assign):  # pragma: no cover
                continue
            yield from _get_contracts([expr.value])


def _resolve_inherit(contract: Attr) -> Iterator[ContractInfo]:
    if not isinstance(contract, astroid.Attribute):
        return
    cls = _get_parent_class(contract)
    if cls is None:
        return
    func = _get_parent_func(contract)
    for base_class in cls.ancestors():
        assert isinstance(base_class, astroid.ClassDef)
        for method in base_class.mymethods():
            assert isinstance(method, astroid.FunctionDef)
            if method.name != func.name:
                continue
            yield from get_contracts(method)


def _get_parent_class(node) -> Optional[astroid.ClassDef]:
    if isinstance(node, astroid.ClassDef):
        return node
    if isinstance(node, (astroid.Attribute, astroid.FunctionDef, astroid.Decorators)):
        return _get_parent_class(node.parent)
    return None


def _get_parent_func(node) -> astroid.FunctionDef:
    if isinstance(node, (astroid.Attribute, astroid.Decorators)):
        return _get_parent_func(node.parent)
    assert isinstance(node, astroid.FunctionDef)
    return node
