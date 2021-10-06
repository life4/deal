from typing import Callable, Iterator

from .._decorators import Contracts
from ._wrappers import Contract
from . import _wrappers


ATTR = '__deal_contract'


def get_contracts(func: Callable) -> Iterator[Contract]:
    while True:
        contracts = getattr(func, ATTR, None)
        if isinstance(contracts, Contracts):
            for validator in contracts.pres:
                yield _wrappers.Pre(validator)
            for validator in contracts.posts:
                yield _wrappers.Post(validator)
            for validator in contracts.ensures:
                yield _wrappers.Ensure(validator)
            for validator in contracts.raises:
                yield _wrappers.Raises(validator)
            for validator in contracts.reasons:
                yield _wrappers.Reason(validator)

        if not hasattr(func, '__wrapped__'):
            return
        func = func.__wrapped__  # type: ignore[attr-defined]
