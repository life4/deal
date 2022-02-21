from typing import FrozenSet, Optional, Tuple, Type

from .._cached_property import cached_property
from .._runtime import HasPatcher, RaisesValidator, ReasonValidator, Validator
from .._source import get_validator_source
from .._types import ExceptionType


class Contract:
    """The base class for all contracts returned by `get_contracts`.
    """
    __slots__ = ('_wrapped',)
    _wrapped: Validator

    def __init__(self, wrapped) -> None:
        self._wrapped = wrapped

    @property
    def exception(self) -> ExceptionType:
        """The exception raised if the contract is not satisfied.
        """
        return self._wrapped.exception

    @property
    def exception_type(self) -> Type[Exception]:
        """The type of the exception raised if the contract is not satisfied.
        """
        return self._wrapped.exception_type

    @property
    def message(self) -> Optional[str]:
        """The message (contract description) provided by user.
        """
        return self._wrapped.message


class ValidatedContract(Contract):
    """The base class for all contracts supporting validation.
    """

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
        self._wrapped.init()
        return get_validator_source(self._wrapped.validator)


class Pre(ValidatedContract):
    """Wrapper for `deal.pre`.
    """


class Post(ValidatedContract):
    """Wrapper for `deal.post`.
    """


class Ensure(ValidatedContract):
    """Wrapper for `deal.ensure`.
    """


class Example(ValidatedContract):
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


class Reason(ValidatedContract):
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
    __slots__ = ('_patcher',)
    _patcher: HasPatcher

    def __init__(self, wrapped) -> None:
        self._patcher = wrapped

    @property
    def exception(self) -> ExceptionType:
        return self._patcher.exception

    @property
    def exception_type(self) -> Type[Exception]:
        return self._patcher.exception_type

    @property
    def message(self) -> Optional[str]:
        return self._patcher.message

    @property
    def markers(self) -> FrozenSet[str]:
        """Side-effects that the function may have.
        """
        return self._patcher.markers
