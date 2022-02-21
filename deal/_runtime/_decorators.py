from functools import partial
from typing import Callable, Optional, Type, TypeVar, Union, overload

from .. import _exceptions
from .._types import ExceptionType
from ._contracts import Contracts
from ._dispatch import Dispatch
from ._has_patcher import HasPatcher
from ._inherit import Inherit
from ._invariant import invariant
from ._validators import InvariantValidator, RaisesValidator, ReasonValidator, Validator


C = TypeVar('C', bound=Callable)
F = TypeVar('F', bound=Callable)
T = TypeVar('T')
TF = TypeVar('TF', bound=Union[Callable, type])


def pre(
    validator,
    *,
    message: Optional[str] = None,
    exception: Optional[ExceptionType] = None,
) -> Callable[[C], C]:
    """Decorator implementing precondition [value] contract.

    [Precondition][wiki] is
    a condition that must be true before the function is executed.
    Raises `PreContractError` otherwise.

    :param validator: a function or validator that implements the contract.
    :param message: error message for the exception raised on contract violation.
        No error message by default.
    :param exception: exception type to raise on the contract violation.
        ``PreContractError`` by default.
    :return: a function wrapper.

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
    contract = Validator(
        validator=validator,
        message=message,
        exception=exception or _exceptions.PreContractError,
    )
    func = partial(Contracts.attach, 'pres', contract)
    return func  # type: ignore[return-value]


def post(
    validator,
    *,
    message: Optional[str] = None,
    exception: Optional[ExceptionType] = None,
) -> Callable[[C], C]:
    """Decorator implementing postcondition [value] contract.

    [Postcondition][wiki] is
    a condition that must be true for the function result.
    Raises `PostContractError` otherwise.

    :param validator: a function or validator that implements the contract.
    :param message: error message for the exception raised on contract violation.
        No error message by default.
    :param exception: exception type to raise on the contract violation.
        ``PostContractError`` by default.
    :return: a function wrapper.

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
    contract = Validator(
        validator=validator,
        message=message,
        exception=exception or _exceptions.PostContractError,
    )
    func = partial(Contracts.attach, 'posts', contract)
    return func  # type: ignore[return-value]


def ensure(
    validator,
    *,
    message: Optional[str] = None,
    exception: Optional[ExceptionType] = None,
) -> Callable[[C], C]:
    """Decorator implementing postcondition [value] contract.

    [Postcondition][wiki] is
    a condition that must be true for the function result.
    Raises `PostContractError` otherwise.
    It's like [@deal.post](#deal.post) but contract accepts as input value
    not only the function result but also the function input arguments.
    The function result is passed into validator as `result` keyword argument.

    :param validator: a function or validator that implements the contract.
    :param message: error message for the exception raised on contract violation.
        No error message by default.
    :param exception: exception type to raise on the contract violation.
        `PostContractError` by default.
    :return: a function wrapper.

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
    contract = Validator(
        validator=validator,
        message=message,
        exception=exception or _exceptions.PostContractError,
    )
    func = partial(Contracts.attach, 'ensures', contract)
    return func  # type: ignore[return-value]


def raises(
    *exceptions: Type[Exception],
    message: Optional[str] = None,
    exception: Optional[ExceptionType] = None,
) -> Callable[[C], C]:
    """Decorator listing the exceptions which the function can raise.

    Implements [exception] contract.
    If the function raises an exception not listed in the decorator,
    `RaisesContractError` will be raised.

    :param exceptions: exceptions which the function can raise.
    :param message: error message for the exception raised on contract violation.
        No error message by default.
    :param exception: exception type to raise on the contract violation.
        `RaisesContractError` by default.
    :return: a function wrapper.

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

    [exception]: https://deal.readthedocs.io/basic/exceptions.html
    """
    contract = RaisesValidator(
        exceptions=exceptions,
        message=message,
        exception=exception or _exceptions.RaisesContractError,
    )
    func = partial(Contracts.attach, 'raises', contract)
    return func  # type: ignore[return-value]


def has(
    *markers: str,
    message: Optional[str] = None,
    exception: Optional[ExceptionType] = None,
) -> Callable[[C], C]:
    """Decorator controlling [side-effects] of the function.

    Allows to specify markers identifying which side-effect the functon may have.
    Side-effects must be propagated into all callers using `deal.has`,
    this is controlled by the [linter].
    Some side-effects are also checked at runtime.


    ```pycon
    >>> import deal
    >>> @deal.has()
    ... def greet():
    ...   print('hello')
    ...
    >>> greet()
    Traceback (most recent call last):
        ...
    SilentContractError
    >>> @deal.has('stdout')
    ... def greet():
    ...   print('hello')
    ...
    >>> greet()
    hello

    ```

    [side-effects]: https://deal.readthedocs.io/basic/side-effects.html
    [linter]: https://deal.readthedocs.io/basic/linter.html
    """
    patcher = HasPatcher(
        markers=markers,
        message=message,
        exception=exception,
    )
    func = partial(Contracts.attach_has, patcher)
    return func  # type: ignore[return-value]


def reason(
    event: Type[Exception],
    validator,
    *,
    message: Optional[str] = None,
    exception: Optional[ExceptionType] = None,
) -> Callable[[C], C]:
    """
    Decorator implementing [exception] contract.

    Allows to assert precondition for raised exception.
    It's like [@deal.ensure](#deal.ensure) but when instead of returning result
    the function raises an exception.

    :param event: exception raising which will trigger contract validation.
    :param validator: a function or validator that implements the contract.
    :param message: error message for the exception raised on contract violation.
        No error message by default.
    :param exception: exception type to raise on the contract violation.
        `ReasonContractError` by default.
    :return: a function wrapper.

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
    ReasonContractError: expected b == 0 (where a=2, b=2)

    ```

    [exception]: https://deal.readthedocs.io/basic/exceptions.html
    """
    contract = ReasonValidator(
        event=event,
        validator=validator,
        message=message,
        exception=exception or _exceptions.ReasonContractError,
    )
    func = partial(Contracts.attach, 'reasons', contract)
    return func  # type: ignore[return-value]


def inv(
    validator,
    *,
    message: Optional[str] = None,
    exception: Optional[ExceptionType] = None,
) -> Callable[[T], T]:
    """
    Decorator implementing invariant [value] contract.

    [Invariant][wiki] is a condition that can be relied upon to be true during execution
    of a program. `@deal.inv` is triggered in 3 cases:

    1. Before class method execution.
    2. After class method execution.
    3. After some class attribute setting.

    Deal doesn't rollback changes on contract violation.

    :param validator: a function or validator that implements the contract.
    :param message: error message for the exception raised on contract violation.
        No error message by default.
    :param exception: exception type to raise on the contract violation.
        `InvContractError` by default.
    :return: a class wrapper.

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
    contract = InvariantValidator(
        validator=validator,
        message=message,
        exception=exception or _exceptions.InvContractError,
    )
    return partial(invariant, contract)


def example(validator: Callable[[], bool]) -> Callable[[C], C]:
    """
    Decorator for providing a usage example for the wrapped function.

    The example isn't checked at runtime.
    Instead, it is run in tests and checked by the linter.
    The example should use the decorated function
    and return True if the result is expected.

    ```pycon
    >>> import deal
    >>> @deal.example(lambda: double(3) == 6)
    ... def double(x):
    ...   return x * 2
    ...

    ```
    """
    contract = Validator(
        validator=validator,
        message=None,
        exception=_exceptions.ExampleContractError,
    )
    func = partial(Contracts.attach, 'examples', contract)
    return func  # type: ignore[return-value]


@overload
def safe(
    *,
    message: Optional[str] = None,
    exception: Optional[ExceptionType] = None,
) -> Callable[[C], C]:
    pass


@overload
def safe(_func: C) -> C:
    pass


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


def chain(*contracts: Callable[[C], C]) -> Callable[[F], F]:
    """Decorator to chain 2 or more contracts together.

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
    """
    def wrapped(func):
        for contract in contracts:
            func = contract(func)
        return func
    return wrapped


def pure(_func: C) -> C:
    """Decorator for [pure functions][wiki].

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


def implies(test, then: T) -> Union[bool, T]:
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


def catch(func: Callable, *args, **kwargs) -> Optional[Type[Exception]]:
    """Call the function with the given arguments, catching any exception.

    The catched exception is returned.
    This function may be useful in combination with {py:func}`deal.example`.

    ```pycon
    >>> import deal
    >>> @deal.example(lambda: deal.catch(div, 4, 0) is ZeroDivisionError)
    ... @deal.raises(ZeroDivisionError)
    ... @deal.reason(ZeroDivisionError, lambda x: x == 0)
    ... def div(x, y):
    ...   return x / y
    ...
    >>>

    ```
    """
    try:
        func(*args, **kwargs)
    except Exception as exc:
        return type(exc)
    return None


def dispatch(func: C) -> Dispatch[C]:
    """Combine multiple functions into one.

    When the decorated function is called, it will try to call all registered
    functions and return the result from the first one that doesn't raise
    `PreContractError`.

    ```pycon
    >>> import deal
    >>> @deal.dispatch
    ... def double(x: int) -> int:
    ...   raise NotImplementedError
    ...
    >>> @double.register
    ... @deal.pre(lambda x: x == 3)
    ... def _(x: int) -> int:
    ...   return 6
    ...
    >>> @double.register
    ... @deal.pre(lambda x: x == 4)
    ... def _(x: int) -> int:
    ...   return 8
    ...
    >>> double(3)
    6
    >>> double(4)
    8
    >>> double(5)
    Traceback (most recent call last):
        ...
    NoMatchError: expected x == 3 (where x=5); expected x == 4 (where x=5)

    ```

    """
    return Dispatch.wrap(func)


def inherit(func: TF) -> TF:
    """Inherit contracts from base classes.

    Can be used to decorate either the whole class or a separate method.

    ```pycon
    >>> import deal
    >>> class Shape:
    ...   @deal.post(lambda r: r > 2)
    ...   def get_sides(self):
    ...     raise NotImplementedError
    ...
    >>> class Triangle(Shape):
    ...   @deal.inherit
    ...   def get_sides(self):
    ...     return 3
    ...
    >>> class Line(Shape):
    ...   @deal.inherit
    ...   def get_sides(self):
    ...     return 2
    ...
    >>> triangle = Triangle()
    >>> triangle.get_sides()
    3
    >>> line = Line()
    >>> line.get_sides()
    Traceback (most recent call last):
        ...
    PreContractError: expected r > 0 (where r=2)

    ```
    """
    return Inherit.wrap(func)
