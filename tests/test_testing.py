# built-in
from typing import NoReturn, TypeVar

# external
import hypothesis
import hypothesis.errors
import hypothesis.strategies
import pytest

# project
import deal


@deal.raises(ZeroDivisionError)
def div1(a: int, b: int) -> float:
    assert isinstance(a, int)
    assert isinstance(b, int)
    return a / b


@deal.pre(lambda a, b: a > 0)
@deal.pre(lambda a, b: b > 0, message='b must be positive')
def div2(a: int, b: int) -> float:
    assert isinstance(a, int)
    assert isinstance(b, int)
    assert a > 0
    assert b > 0
    return a / b


def test_count():
    for count in (1, 10, 20, 50):
        cases = deal.cases(div1, count=count)
        assert len(list(cases)) == count

        cases = deal.cases(div2, count=count)
        assert len(list(cases)) == count


def test_params_detected():
    for case in deal.cases(div1, count=10):
        assert set(case.kwargs) == {'a', 'b'}

    for case in deal.cases(div2, count=10):
        assert set(case.kwargs) == {'a', 'b'}


def test_params_type():
    for case in deal.cases(div1, count=10):
        assert type(case.kwargs['a']) is int
        assert type(case.kwargs['b']) is int

    for case in deal.cases(div2, count=10):
        assert type(case.kwargs['a']) is int
        assert type(case.kwargs['b']) is int


def test_params_ok_with_excs():
    results = []
    for case in deal.cases(div1, count=20):
        result = case()
        results.append(result)
    assert len(results) == 20
    assert any(r is NoReturn for r in results), 'no exception occured'


def test_no_bad_examples():
    for case in deal.cases(div2, count=20):
        assert case.kwargs['a'] > 0
        assert case.kwargs['b'] > 0


def test_return_type_checks():
    def div(a: int, b: int):
        return 1

    for case in deal.cases(div, count=20):
        case()

    def div(a: int, b: int) -> str:
        return 1

    with pytest.raises(TypeError):
        case = next(iter(deal.cases(div, count=20)))
        case()


def test_explicit_kwargs():
    def div(a: int, b: int):
        assert b == 4

    for case in deal.cases(div, kwargs=dict(b=4), count=20):
        case()


def test_explicit_strategy():
    def div(a: int, b: int):
        assert 0 <= b <= 4

    cases = deal.cases(
        div,
        kwargs=dict(b=hypothesis.strategies.integers(min_value=0, max_value=4)),
        count=20,
    )
    for case in cases:
        case()


def test_disable_type_checks():
    def bad(a: int) -> str:
        return a

    # type is wrong and checked
    cases = deal.cases(bad, count=1)
    case = next(iter(cases))
    msg = 'type of the return value must be str; got int instead'
    with pytest.raises(TypeError, match=msg):
        case()

    # type is wrong and ignored
    cases = deal.cases(bad, count=1, check_types=False)
    case = next(iter(cases))
    case()

    def good(a: int) -> int:
        return a

    # type is good
    cases = deal.cases(good, count=1)
    case = next(iter(cases))
    case()


def test_type_var():
    T = TypeVar('T')  # noqa: N806

    def identity(a: T, b) -> T:
        return b

    kwargs = dict(kwargs={}, func=identity, exceptions=(), check_types=True)
    case = deal.TestCase(args=('ab', 'cd'), **kwargs)
    case()

    case = deal.TestCase(args=(['ab'], ['cd', 'ef']), **kwargs)
    case()

    case = deal.TestCase(args=('ab', 1), **kwargs)
    msg = 'type of the return value must be exactly str; got int instead'
    with pytest.raises(TypeError, match=msg):
        case()


@hypothesis.given(
    a=hypothesis.strategies.integers(),
    b=hypothesis.strategies.integers(),
)
def test_hypothesis_div1_smoke(a, b):
    func = deal.hypothesis(div1)
    func(a, b)


@hypothesis.settings(
    suppress_health_check=(
        hypothesis.HealthCheck.filter_too_much,
    ),
)
@hypothesis.given(
    a=hypothesis.strategies.integers(),
    b=hypothesis.strategies.integers(),
)
def test_hypothesis_div2_smoke(a, b):
    func = deal.hypothesis(div2)
    func(a, b)


def test_hypothesis_reject_bad():
    func = deal.hypothesis(div2)
    with pytest.raises(hypothesis.errors.UnsatisfiedAssumption):
        func(a=4, b=-2)


def test_hypothesis_accept_good():
    func = deal.hypothesis(div2)
    func(a=4, b=8)


def test_hypothesis_suppress_raises():
    func = deal.hypothesis(div1)
    result = func(a=4, b=0)
    assert result is NoReturn
