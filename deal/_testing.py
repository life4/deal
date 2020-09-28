# built-in
import typing
from inspect import signature

# external
import hypothesis
import hypothesis.strategies
import typeguard

# app
from ._decorators import Pre, Raises
from ._types import ArgsKwargsType


class TestCase(typing.NamedTuple):
    """A callable object, wrapper around a function that must be tested.

    When called, calls the wrapped function, suppresses expected exceptions,
    checks the type of the result, and returns it.
    """

    args: typing.Tuple[typing.Any, ...]
    """Positional arguments to be passed in the function"""

    kwargs: typing.Dict[str, typing.Any]
    """Keyword arguments to be passed in the function"""

    func: typing.Callable
    """The function which will be called when the test case is called"""

    exceptions: typing.Tuple[typing.Type[Exception], ...]
    """Exceptions that must be suppressed.
    """

    check_types: bool
    """Check that the result matches return type of the function.
    """

    def __call__(self) -> typing.Any:
        """Calls the given test case returning the called functions result on success or
        Raising an exception on error
        """
        try:
            result = self.func(*self.args, **self.kwargs)
        except self.exceptions:
            return typing.NoReturn  # type: ignore
        self._check_result(result)
        return result

    def _check_result(self, result: typing.Any) -> None:
        if not self.check_types:
            return
        hints = typing.get_type_hints(self.func)
        if 'return' not in hints:
            return
        memo = typeguard._CallMemo(
            func=self.func,
            args=self.args,
            kwargs=self.kwargs,
        )
        typeguard.check_argument_types(memo=memo)
        typeguard.check_type(
            argname='the return value',
            value=result,
            expected_type=hints['return'],
            memo=memo,
        )


def get_excs(func: typing.Callable) -> typing.Iterator[typing.Type[Exception]]:
    while True:
        if getattr(func, '__closure__', None):
            for cell in func.__closure__:       # type: ignore
                obj = cell.cell_contents
                if isinstance(obj, Raises):
                    yield from obj.exceptions
                elif isinstance(obj, Pre):
                    if isinstance(obj.exception, Exception):
                        yield type(obj.exception)
                    else:
                        yield obj.exception

        if not hasattr(func, '__wrapped__'):    # type: ignore
            return
        func = func.__wrapped__                 # type: ignore


def get_examples(func: typing.Callable, kwargs: typing.Dict[str, typing.Any],
                 count: int) -> typing.List[ArgsKwargsType]:
    kwargs = kwargs.copy()
    for name, value in kwargs.items():
        if isinstance(value, hypothesis.strategies.SearchStrategy):
            continue
        kwargs[name] = hypothesis.strategies.just(value)

    def pass_along_variables(*args, **kwargs) -> ArgsKwargsType:
        return args, kwargs

    pass_along_variables.__signature__ = signature(func)    # type: ignore
    pass_along_variables.__annotations__ = getattr(func, '__annotations__', {})
    strategy = hypothesis.strategies.builds(pass_along_variables, **kwargs)
    examples = []

    @hypothesis.given(strategy)
    @hypothesis.settings(
        database=None,
        max_examples=count,
        deadline=None,
        verbosity=hypothesis.Verbosity.quiet,
        phases=(hypothesis.Phase.generate,),
        suppress_health_check=hypothesis.HealthCheck.all(),
    )
    def example_generator(ex: ArgsKwargsType) -> None:
        examples.append(ex)

    example_generator()  # pylint: disable=no-value-for-parameter
    return examples


def cases(func: typing.Callable, *, count: int = 50,
          kwargs: typing.Dict[str, typing.Any] = None,
          check_types: bool = True,
          ) -> typing.Iterator[TestCase]:
    """[summary]

    :param func: the function to test. Should be type annotated.
    :type func: typing.Callable
    :param count: how many test cases to generate, defaults to 50.
    :type count: int, optional
    :param kwargs: keyword arguments to pass into the function.
    :type kwargs: typing.Dict[str, typing.Any], optional
    :param check_types: check that the result matches return type of the function.
        Enabled by default.
    :type check_types: bool, optional
    :yield: Emits test cases.
    :rtype: typing.Iterator[TestCase]

    ```pycon
    >>> import deal
    >>> @deal.pre(lambda a, b: b != 0)
    ... def div(a: int, b: int) -> float:
    ...   return a / b
    ...
    >>> cases = deal.cases(div)
    >>> next(cases)
    TestCase(args=(), kwargs=..., func=<function div ...>, exceptions=(<class 'PreContractError'>,))
    >>> case = next(cases)
    >>> case()  # execute the test case
    ...
    ```

    """
    if not kwargs:
        kwargs = {}
    params_generator = get_examples(
        func=func,
        count=count,
        kwargs=kwargs,
    )
    for args, kwargs in params_generator:
        yield TestCase(
            args=args,
            kwargs=kwargs,
            func=func,
            exceptions=tuple(get_excs(func)),
            check_types=check_types,
        )
