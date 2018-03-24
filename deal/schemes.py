

class Scheme(object):
    pass


def is_scheme(obj):
    if isinstance(obj, Scheme):
        return True
    if hasattr(obj, 'mro'):
        for parent in obj.mro():
            if parent.__module__.startswith('djburger.'):
                return True
    return False
