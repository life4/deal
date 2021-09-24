from typing import Callable, FrozenSet, Optional, Tuple, Type

from .. import _decorators
from .._cached_property import cached_property
from .._decorators.base import Base
from .._source import get_validator_source
from .._types import ExceptionType


class Contract:
    """The base class for all contracts returned by `get_contracts`.
    """
    _wrapped: Base

    def __init__(self, wrapped):
        self._wrapped = wrapped

    @property
    def function(self) -> Callable:
        """The function that the contract wraps.
        """
        return self._wrapped.function

    @property
    def exception(self) -> Optional[ExceptionType]:
        """The exception raised if the contract is not satisfied.
        """
        return self._wrapped.exception

    @property
    def message(self) -> Optional[str]:
        """The message (contract description) provided by user.
        """
        return self._wrapped.message


class _ValidatedContract(Contract):
    def validate(self, *args, **kwargs) -> None:
        """Run the validator.

        If validation fails, the `exception` is raised.
        """
        self._wrapped.validate(*args, **kwargs)

    @cached_property
    def source(self) -> str:
        """The source code for the validator function.

        For named functions it is the name of the function.
        For lambdas it is the body of the lambda.
        """
        validator = self._wrapped._make_validator()
        return get_validator_source(validator)


class Pre(_ValidatedContract):
    """Wrapper for `deal.pre`.
    """
    _wrapped: _decorators.Pre


class Post(_ValidatedContract):
    """Wrapper for `deal.post`.
    """
    _wrapped: _decorators.Post


class Ensure(_ValidatedContract):
    """Wrapper for `deal.ensure`.
    """
    _wrapped: _decorators.Ensure


class Raises(Contract):
    """Wrapper for `deal.raises`.
    """
    _wrapped: _decorators.Raises

    @property
    def exceptions(self) -> Tuple[Type[Exception], ...]:
        """Exceptions that the function can raise.
        """
        return self._wrapped.exceptions


class Reason(_ValidatedContract):
    """Wrapper for `deal.reason`.
    """
    _wrapped: _decorators.Reason

    @property
    def event(self) -> Type[Exception]:
        """The exception for which the validator is provided.
        """
        return self._wrapped.event


class Has(Contract):
    """Wrapper for `deal.has`.
    """
    _wrapped: _decorators.Has

    @property
    def markers(self) -> FrozenSet[str]:
        """Side-effects that the function may have.
        """
        return self._wrapped.markers
