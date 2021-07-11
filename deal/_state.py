import os
from typing import Callable, TypeVar


T = TypeVar('T', bound=Callable)


class _State:
    __slots__ = ('debug', 'color')
    debug: bool
    color: bool

    def __init__(self):
        self.reset()

    def reset(self) -> None:
        """Restore contracts switch to default.

        All contracts are disabled on production by default.
        See [runtime][runtime] documentation.

        [runtime]: https://deal.readthedocs.io/basic/runtime.html
        """
        self.debug = __debug__
        self.color = 'NO_COLOR' not in os.environ

    def enable(self) -> None:
        """Enable all contracts.
        """
        self.debug = True

    def disable(self) -> None:
        """Disable all contracts.
        """
        self.debug = False

    def disabled(self, func: T) -> T:
        """Decorator to disable contracts.
        """
        def wrapper(*args, **kwargs):
            old_value = self.debug
            self.debug = False
            try:
                return func(*args, **kwargs)
            finally:
                self.debug = old_value

        return wrapper  # type: ignore[return-value]


state = _State()
reset = state.reset
enable = state.enable
disable = state.disable
