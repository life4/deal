import deal
import pytest
from deal._state import state


@deal.pre(lambda x: x == 3)
def double3(x):
    return 6


@deal.pre(lambda x: x == 4)
def double4(x):
    return 8


def test_match():
    double = deal.dispatch(double3, double4)
    assert double(3) == 6
    assert double(4) == 8


def test_no_match():
    double = deal.dispatch(double3, double4)
    with pytest.raises(deal.NoMatchError) as exc_info:
        double(2)
    state.color = False
    exp = 'expected x == 3 (where x=2); expected x == 4 (where x=2)'
    assert str(exc_info.value) == exp
    state.color = True


def test_match_default():
    double = deal.dispatch(double3, double4, lambda x: x * 2)
    assert double(10) == 20
