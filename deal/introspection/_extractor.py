from __future__ import annotations

from typing import Callable, Iterator, Protocol, TypeVar

from typing_extensions import TypeGuard

from .._runtime import Contracts, Inherit
from . import _wrappers
from ._wrappers import Contract, ValidatedContract


ATTR = '__deal_contract'
F = TypeVar('F', bound=Callable)


class WithWrappedSpecial(Protocol):
    __wrapped__: Callable


def has_wrapped(cobj: Callable) -> TypeGuard[WithWrappedSpecial]:
    return hasattr(cobj, '__wrapped__')


def unwrap(func: F) -> F:
    """Get the original wrapped function without deal contracts.
    """
    contracts = getattr(func, ATTR, None)
    if isinstance(contracts, Contracts):
        return contracts.func
    return func


def init_all(func: Callable) -> None:
    """Call .init() on all contracts.

    This is useful when you need to explicitly precache contracts.
    For example, when profiling the function.
    """
    for contract in get_contracts(func):
        if isinstance(contract, ValidatedContract):
            contract.init()


def get_contracts(func: Callable) -> Iterator[Contract]:
    while True:
        if isinstance(func, Inherit):
            func = func._patch()
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
            for validator in contracts.examples:
                yield _wrappers.Example(validator)
            if contracts.patcher:
                yield _wrappers.Has(contracts.patcher)

        if not has_wrapped(func):
            return
        func = func.__wrapped__
