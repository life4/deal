from .core import Raises, Pre


def get_excs(func):
    while True:
        if func.__closure__:
            for cell in func.__closure__:
                obj = cell.cell_contents
                if isinstance(obj, Raises):
                    yield from obj.exceptions
                elif isinstance(obj, Pre):
                    exc = obj.exception
                    if not isinstance(exc, type):
                        exc = type(exc)
                    yield exc

        if not hasattr(func, '__wrapped__'):
            return
        func = func.__wrapped__


def cases(func, *args, runs: int = 50, **kwargs) -> None:
    from hypothesis_auto.tester import auto_test_cases

    return auto_test_cases(
        *args,
        auto_function_=func,
        auto_allow_exceptions_=tuple(get_excs(func)),
        auto_limit_=runs,
        **kwargs,
    )
