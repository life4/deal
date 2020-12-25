
FUNCTIONS = dict()


def register(name: str):
    def wrapper(func):
        FUNCTIONS[name] = func
        return func
    return wrapper
