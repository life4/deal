

class _State:
    def __init__(self):
        self.reset()

    def reset(self) -> None:
        self.main = True
        self.debug = __debug__

    def switch(self, *, main: bool = None, debug: bool = None) -> None:
        if main is not None:
            self.main = main
        if debug is not None:
            self.debug = debug


state = _State()
reset = state.reset
switch = state.switch
