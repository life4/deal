import os
from typing import Callable, TypeVar


T = TypeVar('T', bound=Callable)
PERMAMENT_ERROR = RuntimeError('contracts are permanently disabled')


class _State:
    __slots__ = ('debug', 'removed', 'color')
    debug: bool
    removed: bool
    color: bool

    def __init__(self) -> None:
        self.removed = False
        self.reset()

    def reset(self) -> None:
        """Restore contracts state to the default.

        All contracts are disabled on production by default.
        See [runtime][runtime] documentation.

        [runtime]: https://deal.readthedocs.io/basic/runtime.html
        """
        if self.removed:
            raise PERMAMENT_ERROR
        self.debug = __debug__
        self.color = 'NO_COLOR' not in os.environ

    def enable(self) -> None:
        """Enable all contracts.
        """
        if self.removed:
            raise PERMAMENT_ERROR
        self.debug = True

    def disable(self, *, permament: bool = False) -> None:
        """Disable all contracts.

        If `permament=True`, then contracts are permanently disabled
        for the current interpreter runtime and cannot be turned on again.
        """
        if self.removed and permament:
            raise PERMAMENT_ERROR
        self.debug = False
        self.removed = permament


state = _State()
reset = state.reset
enable = state.enable
disable = state.disable
