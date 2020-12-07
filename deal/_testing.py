# built-in
import typing
from functools import update_wrapper
from inspect import signature

# external
import hypothesis
import hypothesis.strategies
import typeguard

# app
from ._cached_property import cached_property
from ._decorators import Pre, Raises
from ._types import ArgsKwargsType


F = typing.Callable[..., None]
FuzzInputType = typing.Union[bytes, bytearray, memoryview, typing.BinaryIO]
FuzzType = typing.Callable[[FuzzInputType], typing.Optional[bytes]]


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


class TestCases:
    """Generate test cases for the given function.

    If you're reading it from the documentation rather than source code,
    keep in mind that sphinx skipped some of the docstrings:
    https://github.com/sphinx-doc/sphinx/issues/7787
    """

    func: typing.Callable
    """the function to test. Should be type annotated."""

    count: int
    """how many test cases to generate, defaults to 50."""

    kwargs: typing.Dict[str, typing.Any]
    """keyword arguments to pass into the function."""

    check_types: bool
    """check that the result matches return type of the function. Enabled by default."""

    settings: hypothesis.settings
    """Hypothesis settings to use instead of default ones."""

    seed: typing.Optional[int]
    """Random seed to use when generating test cases. Use it to make tests deterministic."""

    def __init__(
        self,
        func: typing.Callable, *,
        count: int = 50,
        kwargs: typing.Dict[str, typing.Any] = None,
        check_types: bool = True,
        settings: typing.Optional[hypothesis.settings] = None,
        seed: typing.Optional[int] = None,
    ) -> None:
        """
        Create test cases generator.

        ```pycon
        >>> import deal
        >>> @deal.pre(lambda a, b: b != 0)
        ... def div(a: int, b: int) -> float:
        ...   return a / b
        ...
        >>> cases = iter(deal.cases(div))
        >>>
        ```

        """
        self.func = func  # type: ignore
        self.count = count
        self.kwargs = kwargs or {}
        self.check_types = check_types
        self.settings = settings or self._get_default_settings()
        self.seed = seed

    def __iter__(self) -> typing.Iterator[TestCase]:
        """Emits test cases.

        It can be helpful when you want to see what test cases are generated.
        The recommend way is to use `deal.cases` as a decorator instead.

        ```pycon
        >>> import deal
        >>> @deal.pre(lambda a, b: b != 0)
        ... def div(a: int, b: int) -> float:
        ...   return a / b
        ...
        >>> cases = iter(deal.cases(div))
        >>> next(cases)
        TestCase(args=(), kwargs=..., func=<function div ...>, exceptions=(), check_types=True)
        >>> for case in cases:
        ...   result = case()  # execute the test case
        >>>
        ```

        """
        cases: typing.List[TestCase] = []
        test = self(cases.append)
        test()
        yield from cases

    def __repr__(self) -> str:
        fname = getattr(self.func, '__name__', repr(self.func))
        return 'deal.cases({})'.format(fname)

    def make_case(self, *args, **kwargs) -> TestCase:
        """Make test case with the given arguments.
        """
        return TestCase(
            args=args,
            kwargs=kwargs,
            func=self.func,
            exceptions=self.exceptions,
            check_types=self.check_types,
        )

    @cached_property
    def validators(self) -> typing.Tuple[typing.Callable, ...]:
        """Returns pre-condition validators.

        It is used in the process of generating hypothesis strategies
        To let hypothesis more effectively avoid wrong input values.
        """
        return tuple(self._get_validators(self.func))

    @staticmethod
    def _get_validators(func: typing.Any) -> typing.Iterator[typing.Callable]:
        while True:
            if getattr(func, '__closure__', None):
                for cell in func.__closure__:
                    obj = cell.cell_contents
                    if isinstance(obj, Pre):
                        yield obj.validate

            if not hasattr(func, '__wrapped__'):
                return
            func = func.__wrapped__

    @cached_property
    def exceptions(self) -> typing.Tuple[typing.Type[Exception], ...]:
        """
        Returns exceptions that will be suppressed by individual test cases.
        The exceptions are extracted from `@deal.raises` of the tested function.
        """
        return tuple(self._get_excs(self.func))

    @staticmethod
    def _get_excs(func: typing.Any) -> typing.Iterator[typing.Type[Exception]]:
        while True:
            if getattr(func, '__closure__', None):
                for cell in func.__closure__:
                    obj = cell.cell_contents
                    if isinstance(obj, Raises):
                        yield from obj.exceptions

            if not hasattr(func, '__wrapped__'):
                return
            func = func.__wrapped__

    @cached_property
    def strategy(self) -> hypothesis.strategies.SearchStrategy:
        """Hypothesis strategy that is used to generate test cases.
        """
        kwargs = self.kwargs.copy()
        for name, value in kwargs.items():
            if isinstance(value, hypothesis.strategies.SearchStrategy):
                continue
            kwargs[name] = hypothesis.strategies.just(value)

        def pass_along_variables(*args, **kwargs) -> ArgsKwargsType:
            return args, kwargs

        pass_along_variables.__signature__ = signature(self.func)    # type: ignore
        update_wrapper(wrapper=pass_along_variables, wrapped=self.func)
        return hypothesis.strategies.builds(pass_along_variables, **kwargs)

    def _get_default_settings(self) -> hypothesis.settings:
        return hypothesis.settings(
            database=None,
            max_examples=self.count,
            deadline=None,
            verbosity=hypothesis.Verbosity.quiet,
            phases=(hypothesis.Phase.generate,),
            suppress_health_check=hypothesis.HealthCheck.all(),
        )

    @typing.overload
    def __call__(self, test_func: F) -> F:
        """Wrap a function to turn it into a proper Hypothesis test.

        This is the recommend way to use `deal.cases`. It is powerful and extendable.

        ```python
        >>> import deal
        >>> @deal.pre(lambda a, b: b != 0)
        ... def div(a: int, b: int) -> float:
        ...   return a / b
        ...
        >>> @deal.cases(div)
        ... def test_div(case):
        ...   ...     # do something before
        ...   case()  # run the test case
        ...   ...     # do something after
        ...
        >>> test_div()  # run all test cases for `div`
        >>>
        ```

        """

    @typing.overload
    def __call__(self) -> None:
        """Generate and run tests for a function.

        This is the fastest way to generate tests for a function.

        ```python
        >>> import deal
        >>> @deal.pre(lambda a, b: b != 0)
        ... def div(a: int, b: int) -> float:
        ...   return a / b
        ...
        >>> test_div = deal.cases(div)
        >>> test_div()  # run the test
        ```

        """

    @typing.overload
    def __call__(self, buffer: FuzzInputType) -> typing.Optional[bytes]:
        """Use a function as a fuzzing target.

        This is a way to provide a random buffer for Hypothesis.
        It can be helpful for heavy testing of something really critical.

        ```python
        >>> import deal
        >>> @deal.pre(lambda a, b: b != 0)
        ... def div(a: int, b: int) -> float:
        ...   return a / b
        ...
        >>> # For sake of doctest, we just mock fuzzer here
        >>> # but you need to use `import atheris` instead.
        >>> from unittest.mock import Mock
        >>> atheris = Mock()
        >>>
        >>> test_div = deal.cases(div)
        >>> atheris.Setup([], test_div)
        ...
        >>> atheris.Fuzz()
        ...
        ```

        """

    def __call__(self, target=None):
        """Allows deal.cases to be used as decorator, test function, or fuzzing target.
        """
        if target is None:
            self._run()
            return None
        if callable(target):
            return self._wrap(target)
        return self._fuzz(target)

    # a hack to make the test discoverable by pytest
    @property
    def __func__(self) -> F:
        return self._run

    @cached_property
    def _run(self) -> F:
        return self._wrap(lambda case: case())

    @cached_property
    def _fuzz(self) -> FuzzType:
        return self._run.hypothesis.fuzz_one_input

    def _wrap(self, test_func: F) -> F:
        @self.settings
        @hypothesis.given(self.strategy)
        def test_wrapper(ex: ArgsKwargsType) -> None:
            for validator in self.validators:
                try:
                    validator(*ex[0], **ex[1])
                except Exception:
                    hypothesis.reject()
            case = self.make_case(*ex[0], **ex[1])
            test_func(case)

        if self.seed is not None:
            test_wrapper = hypothesis.seed(self.seed)(test_wrapper)
        return test_wrapper


cases = TestCases
