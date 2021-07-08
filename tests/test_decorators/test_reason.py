import pytest

import deal

from .helpers import run_sync


@deal.reason(ValueError, lambda x: x == 1)
def func(x):
    if x == 0:
        raise ZeroDivisionError
    if x == 1:
        raise ValueError
    if x == 2:
        raise ValueError
    return x


def test_reason_just_works():
    assert func(3) == 3


@pytest.mark.parametrize('value, exc', [
    (0, ZeroDivisionError),
    (1, ValueError),
    (2, deal.ReasonContractError),
])
def test_reason_exception(value, exc):
    with pytest.raises(exc):
        func(value)


def test_reason_custom_exc():
    @deal.reason(KeyError, lambda: False, exception=ValueError('hello'))
    def func():
        raise KeyError
    with pytest.raises(ValueError):
        func()


@pytest.mark.parametrize('value, exc', [
    (0, ZeroDivisionError),
    (1, ValueError),
    (2, deal.ReasonContractError),
])
def test_decorating_async_function(value, exc):
    @deal.reason(ValueError, lambda x: x == 1)
    async def func(x):
        if x == 0:
            raise ZeroDivisionError
        if x == 1:
            raise ValueError
        if x == 2:
            raise ValueError
        return x

    assert run_sync(func(3)) == 3
    with pytest.raises(exc):
        run_sync(func(value))


@pytest.mark.parametrize('value, exc', [
    (0, ZeroDivisionError),
    (1, ValueError),
    (2, deal.ReasonContractError),
])
def test_decorating_generator(value, exc):
    @deal.reason(ValueError, lambda x: x == 1)
    def func(x):
        if x == 0:
            raise ZeroDivisionError
        if x == 1:
            raise ValueError
        if x == 2:
            raise ValueError
        yield x

    assert list(func(3)) == [3]
    with pytest.raises(exc):
        list(func(value))
