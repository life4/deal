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


test_div1_short = deal.cases(div1)
test_div2_short = deal.cases(div2)


def test_short_version_is_discoverable():
    from _pytest.python import PyCollector

    collector = PyCollector.__new__(PyCollector)
    collector._matches_prefix_or_glob_option = lambda *args: True
    test = deal.cases(div1)
    assert collector.istestfunction(test, 'test_div') is True


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


@deal.cases(div1)
def test_decorator_div1_smoke(case):
    case()


@deal.cases(div2)
def test_decorator_div2_smoke(case):
    case()


@deal.cases(div2)
def test_decorator_rejects_bad(case):
    assert case.kwargs['a'] > 0
    assert case.kwargs['b'] > 0
    case()


@deal.cases(div1, kwargs=dict(b=0))
def test_decorator_suppress_raises(case):
    result = case()
    assert result is NoReturn


def test_repr():
    def fn():
        pass

    cases = deal.cases(fn)
    assert repr(cases) == 'deal.cases(fn)'


def test_seed():
    c1 = list(deal.cases(div1, seed=12, count=20))
    c2 = list(deal.cases(div1, seed=12, count=20))
    assert c1 == c2

    c3 = list(deal.cases(div1, seed=34, count=20))
    assert c2 != c3


def test_run_ok():
    test = deal.cases(div1)
    res = test()
    assert res is None


def test_run_fail():
    @deal.safe
    def div(a: int, b: int):
        return a / b

    test = deal.cases(div, seed=1)
    with pytest.raises(deal.RaisesContractError):
        test()


def test_fuzz_propagate():
    @deal.safe
    def div(a: str):
        assert type(a) is str
        raise ZeroDivisionError

    cases = deal.cases(div, seed=1)
    with pytest.raises(deal.RaisesContractError):
        cases(b'g`\xf8\xb07\xf8\xea9')


def test_fuzz_bad_input():
    @deal.safe
    def div(a: str):
        raise ZeroDivisionError

    cases = deal.cases(div, seed=1)
    res = cases(b'')
    assert res is None


def test_pass_fixtures():
    @deal.safe
    def div(a: str):
        raise ZeroDivisionError

    @deal.cases(div)
    def test_div1(case, fixt):
        assert fixt == 13
        case()

    with pytest.raises(deal.RaisesContractError):
        test_div1(fixt=13)

    with pytest.raises(deal.RaisesContractError):
        test_div1(13)
