

class _State:
    __slots__ = ('debug', )
    debug: bool

    def __init__(self):
        self.reset()

    def reset(self) -> None:
        """Restore contracts switch to default.

        All contracts are disabled on production by default.
        See [runtime][runtime] documentation.

        [runtime]: https://deal.readthedocs.io/basic/runtime.html
        """
        self.debug = __debug__

    def enable(self) -> None:
        """Enable all contracts.
        """
        self.debug = True

    def disable(self) -> None:
        """Disable all contracts.
        """
        self.debug = False


state = _State()
reset = state.reset
enable = state.enable
disable = state.disable
