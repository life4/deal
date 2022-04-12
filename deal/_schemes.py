from __future__ import annotations

from typing import Any

import vaa


class Scheme:
    """A base class for implementing a custom validator.

    The custom validator should implement `is_valid` method.
    The method should return True if the data is valid.
    Otherwise, it should set `errors` attribute and return False.
    """
    data: dict[str, Any]
    errors: list[vaa.Error]

    def __init__(self, data: dict[str, Any]) -> None:
        self.data = data

    def is_valid(self) -> bool:
        raise NotImplementedError
