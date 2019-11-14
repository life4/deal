import deal
import pytest

from .helpers import run_sync


def test_parameters_and_result_fulfill_constact():
    @deal.ensure(lambda a, b, result: a > 0 and b > 0 and result != 'same number')
    def func(a, b):
        if a == b:
            return 'same number'
        else:
            return 'different numbers'

    assert func(1, 2) == 'different numbers'
    with pytest.raises(deal.PostContractError):
        func(0, 1)
    with pytest.raises(deal.PostContractError):
        func(1, 0)
    with pytest.raises(deal.PostContractError):
        func(1, 1)


def test_decorating_async_function():
    @deal.ensure(lambda a, b, result: a > 0 and b > 0 and result != 'same number')
    async def func(a, b):
        if a == b:
            return 'same number'
        else:
            return 'different numbers'

    assert run_sync(func(1, 2)) == 'different numbers'
    with pytest.raises(deal.PostContractError):
        run_sync(func(0, 1))
