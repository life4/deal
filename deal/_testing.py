# built-in
import typing
from functools import update_wrapper
from inspect import signature

# external
import hypothesis
import hypothesis.strategies
import typeguard
from hypothesis.internal.reflection import proxies

# app
from ._cached_property import cached_property
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


def get_excs(func: typing.Any) -> typing.Iterator[typing.Type[Exception]]:
    while True:
        if getattr(func, '__closure__', None):
            for cell in func.__closure__:
                obj = cell.cell_contents
                if isinstance(obj, Raises):
                    yield from obj.exceptions

        if not hasattr(func, '__wrapped__'):
            return
        func = func.__wrapped__


def get_validators(func: typing.Any) -> typing.Iterator[typing.Callable]:
    """Returns pre-condition validators.

    It is used in the process of generating hypothesis strategies
    To let hypothesis more effectively avoid wrong input values.
    """
    while True:
        if getattr(func, '__closure__', None):
            for cell in func.__closure__:
                obj = cell.cell_contents
                if isinstance(obj, Pre):
                    yield obj.validate

        if not hasattr(func, '__wrapped__'):
            return
        func = func.__wrapped__


def get_examples(
    func: typing.Callable,
    kwargs: typing.Dict[str, typing.Any],
    count: int,
) -> typing.List[ArgsKwargsType]:
    kwargs = kwargs.copy()
    for name, value in kwargs.items():
        if isinstance(value, hypothesis.strategies.SearchStrategy):
            continue
        kwargs[name] = hypothesis.strategies.just(value)

    def pass_along_variables(*args, **kwargs) -> ArgsKwargsType:
        return args, kwargs

    pass_along_variables.__signature__ = signature(func)    # type: ignore
    update_wrapper(wrapper=pass_along_variables, wrapped=func)
    strategy = hypothesis.strategies.builds(pass_along_variables, **kwargs)
    validators = tuple(get_validators(func))
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
        for validator in validators:
            try:
                validator(*ex[0], **ex[1])
            except Exception:
                hypothesis.reject()
        examples.append(ex)

    example_generator()  # pylint: disable=no-value-for-parameter
    return examples


def cases(
    func: typing.Callable, *,
    count: int = 50,
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
    exceptions = tuple(get_excs(func))
    for args, kwargs in params_generator:
        yield TestCase(
            args=args,
            kwargs=kwargs,
            func=func,
            exceptions=exceptions,
            check_types=check_types,
        )


class HypothesisWrapper:
    func: typing.Callable
    check_types: bool = True

    def __init__(self, func: typing.Callable, check_types: bool):
        self.func = func  # type: ignore
        self.check_types = check_types

    @cached_property
    def validators(self):
        return tuple(get_validators(self.func))

    @cached_property
    def exceptions(self):
        return tuple(get_excs(self.func))

    def make_case(self, *args, **kwargs) -> TestCase:
        return TestCase(
            args=args,
            kwargs=kwargs,
            func=self.func,
            exceptions=self.exceptions,
            check_types=self.check_types,
        )

    def __call__(self, *args, **kwargs):
        for validator in self.validators:
            try:
                validator(*args, **kwargs)
            except Exception:
                hypothesis.reject()
        case = self.make_case(*args, **kwargs)
        return case()


def hypothesis_wrapper(func: typing.Callable, check_types: bool = True) -> HypothesisWrapper:
    """Wrapper for a function to communicate back into [hypothesis][hypothesis] contract violations.

    ```pycon
    >>> import deal
    >>> import hypothesis
    >>> import hypothesis.strategies as st

    >>> @deal.raises(ZeroDivisionError)
    >>> def div(a: int, b: int) -> float:
    ...     return a / b

    >>> @hypothesis.given(
    ...     a=st.integers(),
    ...     b=st.integers(),
    ... )
    ... def test_div(a, b):
    ...     func = deal.hypothesis(div)
    ...     func(a, b)
    ...
    >>> test_div()
    ```
    See [hypothesis integration][hypoint] documentation for more details.

    [hypothesis]: https://hypothesis.readthedocs.io/en/latest/
    [hypoint]: https://deal.readthedocs.io/details/tests.html#hypothesis-integration
    """
    wrapper = HypothesisWrapper(
        func=func,
        check_types=check_types,
    )
    return proxies(func)(wrapper)
