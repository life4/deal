import pytest

import deal
from deal._state import state


@deal.pre(lambda x: x == 3)
def double3(x: int) -> int:
    return 6


@deal.pre(lambda x: x == 4)
def double4(x: int) -> int:
    return 8


def double(x: int) -> int:
    """Documentation"""
    raise NotImplementedError


def test_docstring():
    f = deal.dispatch(double)
    f.register(double3)
    assert f.__doc__ == 'Documentation'


def test_match():
    f = deal.dispatch(double)
    f.register(double3)
    f.register(double4)
    assert f(3) == 6
    assert f(4) == 8


def test_no_match():
    f = deal.dispatch(double)
    f.register(double3)
    f.register(double4)
    with pytest.raises(deal.NoMatchError) as exc_info:
        f(2)
    state.color = False
    exp = 'expected x == 3 (where x=2); expected x == 4 (where x=2)'
    assert str(exc_info.value) == exp
    state.color = True


def test_match_default():
    f = deal.dispatch(double)
    f.register(double3)
    f.register(double4)
    f.register(lambda x: x * 2)
    assert f(10) == 20
