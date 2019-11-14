import deal
import pytest

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
