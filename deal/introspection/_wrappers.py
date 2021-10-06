from typing import Callable, FrozenSet, Optional, Tuple, Type

from .._runtime import Validator, RaisesValidator, ReasonValidator, HasPatcher
from .._cached_property import cached_property
from .._source import get_validator_source
from .._types import ExceptionType


class Contract:
    """The base class for all contracts returned by `get_contracts`.
    """
    _wrapped: Validator

    def __init__(self, wrapped):
        self._wrapped = wrapped

    @property
    def function(self) -> Callable:
        """The function that the contract wraps.
        """
        return self._wrapped.function

    @property
    def exception(self) -> ExceptionType:
        """The exception raised if the contract is not satisfied.
        """
        return self._wrapped.exception

    @property
    def exception_type(self) -> Type[Exception]:
        return self._wrapped.exception_type

    @property
    def message(self) -> Optional[str]:
        """The message (contract description) provided by user.
        """
        return self._wrapped.message


class _ValidatedContract(Contract):
    def init(self) -> None:
        """Initialize the contract.

        This method is called when the contract is validated in the first time.
        It includes some costly operations, like introspection of the wrapped function.
        You can call it manually if you want to initialize the contract before validation.
        For instance, if you need a consistent execution time for the function.
        """
        self._wrapped.init()

    def validate(self, *args, **kwargs) -> None:
        """Run the validator.

        If validation fails, the `exception` is raised.
        """
        self._wrapped.validate(args, kwargs)

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


class Post(_ValidatedContract):
    """Wrapper for `deal.post`.
    """


class Ensure(_ValidatedContract):
    """Wrapper for `deal.ensure`.
    """


class Example(_ValidatedContract):
    """Wrapper for `deal.example`.
    """


class Raises(Contract):
    """Wrapper for `deal.raises`.
    """
    _wrapped: RaisesValidator

    @property
    def exceptions(self) -> Tuple[Type[Exception], ...]:
        """Exceptions that the function can raise.
        """
        return self._wrapped.exceptions


class Reason(_ValidatedContract):
    """Wrapper for `deal.reason`.
    """
    _wrapped: ReasonValidator

    @property
    def event(self) -> Type[Exception]:
        """The exception for which the validator is provided.
        """
        return self._wrapped.event


class Has(Contract):
    """Wrapper for `deal.has`.
    """
    _wrapped: HasPatcher

    @property
    def markers(self) -> FrozenSet[str]:
        """Side-effects that the function may have.
        """
        return self._wrapped.markers
