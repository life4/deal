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


class TestCases:
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

    func: typing.Callable
    count: int
    kwargs: typing.Dict[str, typing.Any]
    check_types: bool

    def __init__(
        self,
        func: typing.Callable, *,
        count: int = 50,
        kwargs: typing.Dict[str, typing.Any] = None,
        check_types: bool = True,
    ) -> None:
        self.func = func
        self.count = kwargs
        self.count = count
        self.kwargs = kwargs
        self.check_types = check_types

    def __iter__(self) -> typing.Iterator[TestCase]:
        cases = []
        test = self(cases.append)
        test()
        yield from cases

    def __repr__(self) -> str:
        fname = getattr(self.func, '__name__', repr(self.func))
        return 'deal.cases({})'.format(fname)

    def make_case(self, *args, **kwargs) -> TestCase:
        return TestCase(
            args=args,
            kwargs=kwargs,
            func=self.func,
            exceptions=self.exceptions,
            check_types=self.check_types,
        )

    @cached_property
    def validators(self) -> typing.Tuple[typing.Callable, ...]:
        return tuple(get_validators(self.func))

    @cached_property
    def exceptions(self) -> typing.Tuple[typing.Type[Exception], ...]:
        return tuple(get_excs(self.func))

    @cached_property
    def strategy(self) -> hypothesis.strategies.SearchStrategy:
        kwargs = (self.kwargs or {}).copy()
        for name, value in kwargs.items():
            if isinstance(value, hypothesis.strategies.SearchStrategy):
                continue
            kwargs[name] = hypothesis.strategies.just(value)

        def pass_along_variables(*args, **kwargs) -> ArgsKwargsType:
            return args, kwargs

        pass_along_variables.__signature__ = signature(self.func)    # type: ignore
        update_wrapper(wrapper=pass_along_variables, wrapped=self.func)
        return hypothesis.strategies.builds(pass_along_variables, **kwargs)

    def __call__(self, test_func: typing.Callable) -> typing.Callable:
        @hypothesis.given(self.strategy)
        @hypothesis.settings(
            database=None,
            max_examples=self.count,
            deadline=None,
            verbosity=hypothesis.Verbosity.quiet,
            phases=(hypothesis.Phase.generate,),
            suppress_health_check=hypothesis.HealthCheck.all(),
        )
        def test_wrapper(ex: ArgsKwargsType) -> None:
            for validator in self.validators:
                try:
                    validator(*ex[0], **ex[1])
                except Exception:
                    hypothesis.reject()
            case = self.make_case(*ex[0], **ex[1])
            test_func(case)

        return test_wrapper


cases = TestCases
