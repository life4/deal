# built-in
from typing import Callable, Type, TypeVar, overload

# app
from . import _decorators
from ._types import ExceptionType


_CallableType = TypeVar('_CallableType', bound=Callable)
_T = TypeVar('_T')


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
    cls = _decorators.Pre[_CallableType]
    return cls(validator=validator, message=message, exception=exception)


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
    cls = _decorators.Post[_CallableType]
    return cls(validator=validator, message=message, exception=exception)


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
        `PostContractError` by default.
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
    cls = _decorators.Ensure[_CallableType]
    return cls(validator=validator, message=message, exception=exception)


def raises(
    *exceptions: Type[Exception],
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
    event: Type[Exception],
    validator,
    *,
    message: str = None,
    exception: ExceptionType = None,
) -> Callable[[_CallableType], _CallableType]:
    """
    Decorator implementing [exception][exception] contract.
    Allows to assert precondition for raised exception.
    It's like [@deal.ensure](#deal.ensure) but when instead of returning result
    the function raises an exception.

    :param event: exception raising which will trigger contract validation.
    :type event: Type[Exception].
    :param validator: a function or validator that implements the contract.
    :param message: error message for the exception raised on contract violation.
        No error message by default.
    :type message: str, optional
    :param exception: exception type to raise on the contract violation.
        `InvContractError` by default.
    :type exception: ExceptionType, optional
    :return: a class wrapper.
    :rtype: Callable[[_T], _T]

    ```pycon
    >>> import deal
    >>> @deal.reason(ZeroDivisionError, lambda a, b: b == 0)
    ... def div(a, b):
    ...   return a / (a - b)
    >>> div(2, 1)
    2.0
    >>> div(0, 0)
    Traceback (most recent call last):
        ...
    ZeroDivisionError: division by zero
    >>> div(2, 2)
    Traceback (most recent call last):
        ...
     ZeroDivisionError: division by zero
     The above exception was the direct cause of the following exception:
        ...
    ReasonContractError

    ```

    [exception]: ../basic/exceptions.md
    """
    cls = _decorators.Reason[_CallableType]
    return cls(event=event, validator=validator, message=message, exception=exception)


def inv(
    validator,
    *,
    message: str = None,
    exception: ExceptionType = None,
) -> Callable[[_T], _T]:
    """
    Decorator implementing invariant [value][value] contract.

    [Invariant][wiki] is a condition that can be relied upon to be true during execution
    of a program. `@deal.inv` is triggered in 3 cases:

    1. Before class method execution.
    2. After class method execution.
    3. After some class attribute setting.

    Deal doesn't rollback changes on contract violation.

    :param validator: a function or validator that implements the contract.
    :param message: error message for the exception raised on contract violation.
        No error message by default.
    :type message: str, optional
    :param exception: exception type to raise on the contract violation.
        `InvContractError` by default.
    :type exception: ExceptionType, optional
    :return: a class wrapper.
    :rtype: Callable[[_T], _T]

    ```pycon
    >>> import deal
    >>> @deal.inv(lambda obj: obj.likes >= 0)
    ... class Video:
    ...   likes = 1
    ...   def like(self): self.likes += 1
    ...   def dislike(self): self.likes -= 1
    ...
    >>> v = Video()
    >>> v.dislike()
    >>> v.likes
    0
    >>> v.dislike()
    Traceback (most recent call last):
    ...
    InvContractError
    >>> v.likes
    -1
    >>> v.likes = 2
    >>> v.likes = -2
    Traceback (most recent call last):
    ...
    InvContractError
    >>> v.likes
    -2

    ```

    [wiki]: https://en.wikipedia.org/wiki/Class_invariant
    [value]: ../basic/values.md
    """
    cls = _decorators.Invariant[_CallableType]
    return cls(validator=validator, message=message, exception=exception)


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
    """
    Alias for [@deal.raises()](#deal.raises).
    Wraps a function that never raises an exception.

    ```pycon
    >>> import deal
    >>> @deal.safe
    ... def div(a, b):
    ...   return a / b
    ...
    >>> div(2, 4)
    0.5
    >>> div(2, 0)
    Traceback (most recent call last):
        ...
     ZeroDivisionError: division by zero
     The above exception was the direct cause of the following exception:
        ...
    RaisesContractError

    ```
    """
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
    """
    Decorator for [pure functions][wiki].
    Alias for `@deal.chain(deal.has(), deal.safe)`.

    Pure function has no side-effects and doesn't raise any exceptions.

    [wiki]: https://en.wikipedia.org/wiki/Pure_function
    """
    return chain(has(), safe)(_func)
