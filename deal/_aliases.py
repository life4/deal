from typing import Callable, Type, TypeVar, Union, overload

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
    PreContractError: expected a + b > 0 (where a=1, b=-2)

    ```

    [wiki]: https://en.wikipedia.org/wiki/Precondition
    [value]: https://deal.readthedocs.io/basic/values.html
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
    PostContractError: expected res > 0 (where res=-1)

    ```

    [wiki]: https://en.wikipedia.org/wiki/Postcondition
    [value]: https://deal.readthedocs.io/basic/values.html
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
    Decorator implementing postcondition [value] contract.
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
    PostContractError: expected a < result (where result=0, a=0)

    ```

    [wiki]: https://en.wikipedia.org/wiki/Postcondition
    [value]: https://deal.readthedocs.io/basic/values.html
    """
    cls = _decorators.Ensure[_CallableType]
    return cls(validator=validator, message=message, exception=exception)


def raises(
    *exceptions: Type[Exception],
    message: str = None,
    exception: ExceptionType = None,
) -> Callable[[_CallableType], _CallableType]:
    """
    Decorators listing exceptions which the function can raise.
    Implements the most important [exception] contract.
    If the function raises an exception not listed in the decorator,
    `RaisesContractError` will be raised.

    :param exceptions: exceptions which the function can raise.
    :type exceptions: Type[Exception].
    :param message: error message for the exception raised on contract violation.
        No error message by default.
    :type message: str, optional
    :param exception: exception type to raise on the contract violation.
        `RaisesContractError` by default.
    :type exception: ExceptionType, optional
    :return: a function wrapper.
    :rtype: Callable[[_T], _T]

    ```pycon
    >>> import deal
    >>> @deal.raises(ZeroDivisionError, ValueError)
    ... def div(a, b):
    ...   return a / b
    ...
    >>> div(1, 0)
    Traceback (most recent call last):
        ...
    ZeroDivisionError: division by zero
    >>> div(1, '')
    Traceback (most recent call last):
        ...
     TypeError: unsupported operand type(s) for /: 'int' and 'str'
     The above exception was the direct cause of the following exception:
        ...
    RaisesContractError

    ```

    [exception] https://deal.readthedocs.io/basic/exceptions.html
    """
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
    Decorator implementing [exception] contract.
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
        `ReasonContractError` by default.
    :type exception: ExceptionType, optional
    :return: a function wrapper.
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

    [exception]: https://deal.readthedocs.io/basic/exceptions.html
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
    InvContractError: expected obj.likes >= 0
    >>> v.likes
    -1
    >>> v.likes = 2
    >>> v.likes = -2
    Traceback (most recent call last):
    ...
    InvContractError: expected obj.likes >= 0
    >>> v.likes
    -2

    ```

    [wiki]: https://en.wikipedia.org/wiki/Class_invariant
    [value]: https://deal.readthedocs.io/basic/values.html
    """
    cls = _decorators.Invariant[_CallableType]
    return cls(  # type: ignore
        validator=validator,
        message=message,
        exception=exception,
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
    """
    Decorator to chain 2 or more contracts together.
    It can be helpful to store contracts separately from the function.
    Consider using it when you have too many contracts.
    Otherwise, the function will be lost under a bunch of decorators.

    ```pycon
    >>> import deal
    >>> sum_contract = deal.chain(
    ...   deal.pre(lambda a, b: a > 0),
    ...   deal.pre(lambda a, b: b > 0),
    ...   deal.post(lambda res: res > 0),
    ... )
    >>> @sum_contract
    ... def sum(a, b):
    ...   return a + b
    ...
    >>> sum(2, 3)
    5
    >>> sum(2, -3)
    Traceback (most recent call last):
        ...
    PreContractError: expected b > 0 (where a=2, b=-3)
    >>> sum(-2, 3)
    Traceback (most recent call last):
        ...
    PreContractError: expected a > 0 (where a=-2, b=3)

    ```

    :param contracts: contracts to chain.
    :return: a function wrapper
    :rtype: Callable[[_CallableType], _CallableType]
    """
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

    ```pycon
    >>> import deal
    >>> @deal.pure
    ... def div(a, b, log=False):
    ...   if log:
    ...     print('div called')
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
    >>> div(2, 3, log=True)
    Traceback (most recent call last):
        ...
    SilentContractError

    ```

    [wiki]: https://en.wikipedia.org/wiki/Pure_function
    """
    return chain(has(), safe)(_func)


def implies(test, then: _T) -> Union[bool, _T]:
    """Check `then` only if `test` is true.

    A convenient helper for contracts that must be checked only for some cases.
    It is known as "implication" or [material conditional][wiki].

    ```pycon
    >>> import deal
    >>> deal.implies(False, False)
    True
    >>> deal.implies(False, True)
    True
    >>> deal.implies(True, False)
    False
    >>> deal.implies(True, True)
    True

    ```

    [wiki]: https://en.wikipedia.org/wiki/Material_conditional
    """
    return not test or then


def dispatch(*functions: _CallableType) -> _CallableType:
    return _decorators.Dispatch(functions)  # type: ignore
