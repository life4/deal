import pytest

import deal


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
