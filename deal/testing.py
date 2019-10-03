from .exceptions import PreContractError
from .core import Raises


def get_excs(func):
    while True:
        if func.__closure__:
            for cell in func.__closure__:
                obj = cell.cell_contents
                if isinstance(obj, Raises):
                    yield from obj.exceptions

        if not hasattr(func, '__wrapped__'):
            return
        func = func.__wrapped__


def cases(func, *, args, kwargs, exceptions, runs: int = 50) -> None:
    from hypothesis_auto.tester import auto_test_cases

    all_exceptions = [PreContractError]
    all_exceptions.extend(exceptions)
    all_exceptions.extend(get_excs(func))

    kwargs.update(dict(
        auto_allow_exceptions_=all_exceptions,
        auto_limit_=runs,
    ))

    return auto_test_cases(func, *args, **kwargs)
