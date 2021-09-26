from functools import partial, update_wrapper
from types import MethodType
from typing import Callable, List, TypeVar

from .._exceptions import InvContractError
from .._types import ExceptionType
from .base import Base


T = TypeVar('T', bound=type)
DEAL_ATTRS = frozenset({
    '_deal_patched_method',
    '_deal_validate',
    '_deal_invariants',
})


class InvariantedClass:
    _deal_invariants: List['Invariant']

    def _deal_validate(self) -> None:
        for inv in self._deal_invariants:
            inv.validate(self)

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


class Invariant(Base[T]):
    exception: ExceptionType

    def _init(self, *args, **kwargs):
        self.signature = None
        self.validator = self._make_validator()
        if hasattr(self.validator, 'is_valid'):
            self.validate = self._vaa_validation
        else:
            self.validate = self._simple_validation
        return self.validate(*args, **kwargs)

    def _vaa_validation(self, obj) -> None:  # type: ignore[override]
        return super()._vaa_validation(**vars(obj))

    @classmethod
    def _default_exception(cls) -> ExceptionType:
        return InvContractError

    def __call__(self, _class: T) -> T:
        invs = getattr(_class, '_deal_invariants', None)
        if invs is None:
            patched_class = type(
                _class.__name__ + 'Invarianted',
                (InvariantedClass, _class),
                {'_deal_invariants': [self]},
            )
        else:
            patched_class = type(
                _class.__name__,
                (_class, ),
                {'_deal_invariants': invs + [self]},
            )
        return patched_class  # type: ignore[return-value]
