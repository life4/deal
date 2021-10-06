from functools import partial, update_wrapper
from types import MethodType
from typing import Callable, List, TypeVar

from ._validators import InvariantValidator


T = TypeVar('T', bound=type)
DEAL_ATTRS = frozenset({
    '_deal_patched_method',
    '_deal_validate',
    '_deal_invariants',
})


class InvariantedClass:
    _deal_invariants: List['InvariantValidator']

    def _deal_validate(self) -> None:
        for validator in self._deal_invariants:
            validator.validate((self,), {})

    def _deal_patched_method(self, method: Callable, *args, **kwargs):
        self._deal_validate()
        result = method(*args, **kwargs)
        self._deal_validate()
        return result

    def __getattribute__(self, name: str):
        attr = super().__getattribute__(name)
        if name in DEAL_ATTRS:
            return attr
        if not isinstance(attr, MethodType):
            return attr
        patched_method = partial(self._deal_patched_method, attr)
        return update_wrapper(patched_method, attr)

    def __setattr__(self, name: str, value) -> None:
        super().__setattr__(name, value)
        self._deal_validate()


def invariant(validator: InvariantValidator, _class: T) -> T:
    invs = getattr(_class, '_deal_invariants', None)
    if invs is None:
        patched_class = type(
            _class.__name__ + 'Invarianted',
            (InvariantedClass, _class),
            {'_deal_invariants': [validator]},
        )
    else:
        patched_class = type(
            _class.__name__,
            (_class, ),
            {'_deal_invariants': invs + [validator]},
        )
    return patched_class  # type: ignore[return-value]
