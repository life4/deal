

class _State:
    __slots__ = ('debug', )
    debug: bool

    def __init__(self):
        self.reset()

    def reset(self) -> None:
        self.debug = __debug__

    def enable(self) -> None:
        self.debug = True

    def disable(self) -> None:
        self.debug = False


state = _State()
reset = state.reset
enable = state.enable
disable = state.disable
