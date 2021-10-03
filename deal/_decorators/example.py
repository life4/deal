from typing import Callable, Type

from .._exceptions import ExampleContractError
from .base import CallableType, StaticBase


class Example(StaticBase[CallableType]):
    validator: Callable[[], bool]

    @classmethod
    def _default_exception(cls) -> Type[ExampleContractError]:
        return ExampleContractError
