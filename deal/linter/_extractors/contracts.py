from typing import Iterator, Tuple

import astroid

from .common import TOKENS, get_name


SUPPORTED_CONTRACTS = {
    'deal.has',
    'deal.post',
    'deal.pre',
    'deal.pure',
    'deal.raises',
    'deal.safe',
}
SUPPORTED_MARKERS = {'deal.pure', 'deal.safe'}


def get_contracts(decorators: list) -> Iterator[Tuple[str, list]]:
    for contract in decorators:
        if isinstance(contract, TOKENS.ATTR):
            name = get_name(contract)
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
