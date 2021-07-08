import pytest

import deal

from .helpers import run_sync


def test_return_value_fulfils_contract():
    func = deal.post(lambda x: x > 0)(lambda x: -x)
    assert func(-4) == 4

    with pytest.raises(deal.PostContractError):
        func(4)


def test_decorating_async_function():
    @deal.post(lambda x: x > 0)
    async def func(x):
        return -x

    assert run_sync(func(-2)) == 2
    with pytest.raises(deal.PostContractError):
        run_sync(func(2))


def test_decorating_generator():
    @deal.post(lambda x: x <= 8)
    def double(x):
        yield x
        yield x * 2
        yield x * 4

    assert list(double(2)) == [2, 4, 8]
    with pytest.raises(deal.PostContractError):
        list(double(4))
