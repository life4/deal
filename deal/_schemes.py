

class Scheme:
    def __init__(self, data):
        self.data = data

    def is_valid(self) -> bool:
        raise NotImplementedError
