# built-in
from typing import Callable, TypeVar, overload

# app
from . import _decorators
from ._types import ExceptionType


_CallableType = TypeVar('_CallableType', bound=Callable)


def pre(
    validator,
    *,
    message: str = None,
    exception: ExceptionType = None,
) -> Callable[[_CallableType], _CallableType]:
    """
    Decorator implementing precondition [value][value] contract.
    [Precondition][wiki] is
    a condition that must be true before the function is executed.
    Raises `PreContractError` otherwise.

    :param validator: a function or validator that implements the contract.
    :param message: error message for the exception raised on contract violation.
        No error message by default.
    :type message: str, optional
    :param exception: exception type to raise on the contract violation.
        ``PreContractError`` by default.
    :type exception: ExceptionType, optional
    :return: a function wrapper.
    :rtype: Callable[[_CallableType], _CallableType]

    ```pycon
    >>> import deal
    >>> @deal.pre(lambda a, b: a + b > 0)
    ... def example(a, b):
    ...     return (a + b) * 2
    >>> example(1, 2)
    6
    >>> example(1, -2)
    Traceback (most recent call last):
      ...
    PreContractError

    ```

    [wiki]: https://en.wikipedia.org/wiki/Precondition
    [value]: ../basic/values.md
    """
    return _decorators.Pre[_CallableType](
        validator, message=message, exception=exception,
    )


def post(
    validator,
    *,
    message: str = None,
    exception: ExceptionType = None,
) -> Callable[[_CallableType], _CallableType]:
    """
    Decorator implementing postcondition [value][value] contract.
    [Postcondition][wiki] is
    a condition that must be true for the function result.
    Raises `PostContractError` otherwise.

    :param validator: a function or validator that implements the contract.
    :param message: error message for the exception raised on contract violation.
        No error message by default.
    :type message: str, optional
    :param exception: exception type to raise on the contract violation.
        ``PostContractError`` by default.
    :type exception: ExceptionType, optional
    :return: a function wrapper.
    :rtype: Callable[[_CallableType], _CallableType]

    ```pycon
    >>> import deal
    >>> @deal.post(lambda res: res > 0)
    ... def example(a, b):
    ...     return a + b
    >>> example(-1, 2)
    1
    >>> example(1, -2)
    Traceback (most recent call last):
      ...
    PostContractError

    ```

    [wiki]: https://en.wikipedia.org/wiki/Postcondition
    [value]: ../basic/values.md
    """
    return _decorators.Post[_CallableType](
        validator, message=message, exception=exception,
    )


def ensure(
    validator,
    *,
    message: str = None,
    exception: ExceptionType = None,
) -> Callable[[_CallableType], _CallableType]:
    """
    Decorator implementing postcondition [value][value] contract.
    [Postcondition][wiki] is
    a condition that must be true for the function result.
    Raises `PostContractError` otherwise.
    It's like [@deal.post](#deal.post) but contract accepts as input value
    not only the function result but also the function input arguments.
    The function result is passed into validator as `result` keyword argument.

    :param validator: a function or validator that implements the contract.
    :param message: error message for the exception raised on contract violation.
        No error message by default.
    :type message: str, optional
    :param exception: exception type to raise on the contract violation.
        ``PostContractError`` by default.
    :type exception: ExceptionType, optional
    :return: a function wrapper.
    :rtype: Callable[[_CallableType], _CallableType]

    ```pycon
    >>> import deal
    >>> @deal.ensure(lambda a, result: a < result)
    ... def example(a):
    ...     return a * 2
    >>> example(2)
    4
    >>> example(0)
    Traceback (most recent call last):
      ...
    PostContractError

    ```

    [wiki]: https://en.wikipedia.org/wiki/Postcondition
    [value]: ../basic/values.md
    """
    return _decorators.Ensure[_CallableType](
        validator, message=message, exception=exception,
    )


def raises(
    *exceptions: Exception,
    message: str = None,
    exception: ExceptionType = None,
) -> Callable[[_CallableType], _CallableType]:
    cls = _decorators.Raises[_CallableType]
    return cls(*exceptions, message=message, exception=exception)


def has(
    *markers: str,
    message: str = None,
    exception: ExceptionType = None,
) -> Callable[[_CallableType], _CallableType]:
    cls = _decorators.Has[_CallableType]
    return cls(*markers, message=message, exception=exception)


def reason(
    event: Exception,
    validator,
    *,
    message: str = None,
    exception: ExceptionType = None,
) -> Callable[[_CallableType], _CallableType]:
    return _decorators.Reason[_CallableType](
        event, validator, message=message, exception=exception,
    )


def inv(
    validator,
    *,
    message: str = None,
    exception: ExceptionType = None,
) -> Callable[[_CallableType], _CallableType]:
    """
    Decorator implementing invariant [value][value] contract.

    [Invariant][wiki] is a condition that can be relied upon to be true during execution
    of a program. `@deal.inv` is triggered in 3 cases:

    1. Before class method execution.
    2. After class method execution.
    3. After some class attribute setting.

    [wiki]: https://en.wikipedia.org/wiki/Invariant_(computer_science)
    [value]: ../basic/values.md
    """
    return _decorators.Invariant[_CallableType](
        validator, message=message, exception=exception,
    )


@overload
def safe(
    *,
    message: str = None,
    exception: ExceptionType = None,
) -> Callable[[_CallableType], _CallableType]:
    pass  # pragma: no cover


@overload
def safe(_func: _CallableType) -> _CallableType:
    pass  # pragma: no cover


def safe(_func=None, **kwargs):
    if _func is None:
        return raises(**kwargs)
    return raises()(_func)


def chain(*contracts) -> Callable[[_CallableType], _CallableType]:
    def wrapped(func):
        for contract in contracts:
            func = contract(func)
        return func
    return wrapped


def pure(_func: _CallableType) -> _CallableType:
    return chain(has(), safe)(_func)


if __name__ == '__main__':
    import doctest
    doctest.testmod()
