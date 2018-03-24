

class Scheme(object):
    pass


def is_scheme(obj):
    if isinstance(obj, Scheme):
        return True
    if 'djburger.' in obj.__module__:
        return True
    return False
