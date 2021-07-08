import pytest

import deal

from .helpers import run_sync


def test_safe():
    func = deal.safe(lambda x: 1 / x)
    func(2)
    with pytest.raises(deal.RaisesContractError):
        func(0)


def test_decorating_async_function():
    @deal.safe
    async def func(x):
        return 10 / x

    assert run_sync(func(2)) == 5
    with pytest.raises(deal.RaisesContractError):
        run_sync(func(0))
