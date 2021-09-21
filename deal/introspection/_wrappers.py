from typing import Callable, FrozenSet, Optional, Tuple, Type
from .._cached_property import cached_property
from .._decorators.base import Base
from .. import _decorators
from .._source import get_validator_source
from .._types import ExceptionType


class Contract:
    _wrapped: Base

    def __init__(self, wrapped):
        self._wrapped = wrapped

    @property
    def function(self) -> Callable:
        return self._wrapped.function

    @property
    def exception(self) -> Optional[ExceptionType]:
        return self._wrapped.exception

    @property
    def message(self) -> Optional[str]:
        return self._wrapped.message


class _ValidatedContract(Contract):
    def validate(self, *args, **kwargs) -> None:
        self._wrapped.validate(*args, **kwargs)

    @cached_property
    def source(self) -> str:
        validator = self._wrapped._make_validator()
        return get_validator_source(validator)


class Pre(_ValidatedContract):
    _wrapped: _decorators.Pre


class Post(_ValidatedContract):
    _wrapped: _decorators.Post


class Ensure(_ValidatedContract):
    _wrapped: _decorators.Ensure


class Raises(Contract):
    _wrapped: _decorators.Raises

    @property
    def exceptions(self) -> Tuple[Type[Exception], ...]:
        return self._wrapped.exceptions


class Reason(_ValidatedContract):
    _wrapped: _decorators.Reason

    @property
    def event(self) -> Type[Exception]:
        return self._wrapped.event


class Has(Contract):
    _wrapped: _decorators.Has

    @property
    def markers(self) -> FrozenSet[str]:
        return self._wrapped.markers
