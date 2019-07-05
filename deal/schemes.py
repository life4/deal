

class Scheme:
    def __init__(self, data, request=None):
        self.data = data

    def is_valid(self) -> bool:
        raise NotImplementedError  # pragma: no cover


def is_scheme(obj) -> bool:
    if not hasattr(obj, 'mro'):
        return False
    if Scheme in obj.mro():
        return True
    for parent in obj.mro():
        if parent.__module__.startswith('djburger.'):
            return True
    return False
