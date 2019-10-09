import deal
import pytest
from typing import NoReturn


@deal.raises(ZeroDivisionError)
@deal.pre(lambda a, b: a > 0)
@deal.pre(lambda a, b: b > 0, message='b must be positive')
def div(a: int, b: int) -> float:
    assert isinstance(a, int)
    assert isinstance(b, int)
    assert a > 0
    assert b > 0
    return a / b


func = div


def test_count():
    for count in (1, 10, 20, 50):
        cases = deal.cases(func, count=count)
        assert len(list(cases)) == count


def test_params_detected():
    for case in deal.cases(func, count=10):
        assert set(case.kwargs) == {'a', 'b'}


def test_params_type():
    for case in deal.cases(func, count=10):
        assert type(case.kwargs['a']) is int
        assert type(case.kwargs['b']) is int


def test_params_ok_with_excs():
    results = []
    for case in deal.cases(func, count=20):
        result = case()
        results.append(result)
    assert any(r is not NoReturn for r in results), 'exception occured on every run'
    assert any(r is NoReturn for r in results), 'no exception occured'


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
