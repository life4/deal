import pytest

import deal

from .helpers import run_sync


def test_parameters_and_result_fulfill_constact():
    @deal.ensure(lambda a, b, result: a > 0 and b > 0 and result != 'same number')
    def func(a, b) -> str:
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


def test_simple_signature():
    @deal.ensure(lambda _: _.a > 0 and _.b > 0 and _.result != 'same number')
    def func(a, b) -> str:
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
    async def func(a, b) -> str:
        if a == b:
            return 'same number'
        else:
            return 'different numbers'

    assert run_sync(func(1, 2)) == 'different numbers'
    with pytest.raises(deal.PostContractError):
        run_sync(func(0, 1))


def test_decorating_generator():
    @deal.ensure(lambda x, y, result: result > y ** 2)
    def multiply(x, y):
        yield x * y
        yield x * y * 2
        yield x * y * 4

    assert list(multiply(2, 1)) == [2, 4, 8]
    with pytest.raises(deal.PostContractError):
        list(multiply(2, 2))


def test_recursive_contracts_ok():
    @deal.ensure(lambda a, b, result: add(result, b) == a)
    def sub(a, b):
        return a - b

    @deal.ensure(lambda a, b, result: sub(result, b) == a)
    def add(a, b):
        return a + b

    assert sub(5, 3) == 2
    assert add(2, 3) == 5
