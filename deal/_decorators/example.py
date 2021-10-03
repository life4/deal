from typing import Callable, Type

from .._exceptions import ExampleContractError
from .base import StaticBase, CallableType


class Example(StaticBase[CallableType]):
    validator: Callable[[], bool]

    @classmethod
    def _default_exception(cls) -> Type[ExampleContractError]:
        return ExampleContractError
