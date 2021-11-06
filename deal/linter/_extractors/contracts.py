import ast
from typing import Iterator, List, Optional, Tuple, Union, overload

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


@overload
def get_contracts(node: ast.expr) -> Iterator[Tuple[str, List[ast.expr]]]:
    pass


@overload
def get_contracts(node: astroid.Expr) -> Iterator[Tuple[str, List[astroid.Expr]]]:
    pass


def get_contracts(decorators):
    for contract in decorators:
        if isinstance(contract, TOKENS.ATTR):
            name = get_name(contract)
            if name == 'deal.inherit':
                yield from _resolve_inherit(contract)
            if name not in SUPPORTED_MARKERS:
                continue
            yield name.split('.')[-1], []

        if isinstance(contract, TOKENS.CALL):
            if not isinstance(contract.func, TOKENS.ATTR):
                continue
            name = get_name(contract.func)
            if name == 'deal.chain':
                yield from get_contracts(contract.args)
            if name not in SUPPORTED_CONTRACTS:
                continue
            yield name.split('.')[-1], contract.args

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
            yield from get_contracts([expr.value])


def _resolve_inherit(contract: Attr) -> Iterator[Tuple[str, List[astroid.Expr]]]:
    if not isinstance(contract, astroid.Attribute):
        return
    cls = _get_parent_class(contract)
    if cls is None:
        return
    for base_class in cls.ancestors():
        assert isinstance(base_class, astroid.ClassDef)
        for method in base_class.mymethods():
            assert isinstance(method, astroid.FunctionDef)
            decorators = method.decorators
            if not isinstance(decorators, astroid.Decorators):
                continue
            yield from get_contracts(decorators.nodes)


def _get_parent_class(node) -> Optional[astroid.ClassDef]:
    if isinstance(node, astroid.ClassDef):
        return node
    if isinstance(node, (astroid.Attribute, astroid.FunctionDef, astroid.Decorators)):
        return _get_parent_class(node.parent)
    return None
