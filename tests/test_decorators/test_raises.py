import pytest
import urllib3

import deal

from .helpers import run_sync


def test_raises_expects_function_to_raise_error():
    func = deal.raises(ZeroDivisionError, ValueError)(lambda x: 1 / x)
    with pytest.raises(ZeroDivisionError):
        func(0)
    func(2)

    func = deal.raises(KeyError)(lambda x: 1 / x)
    with pytest.raises(deal.RaisesContractError):
        func(0)


def test_raises_doesnt_override_another_contract():
    @deal.raises(ZeroDivisionError)
    @deal.has()
    def func(do, number):
        if do:
            http = urllib3.PoolManager()
            http.request('GET', 'http://httpbin.org/robots.txt')
        return 1 / number

    assert func(False, 1) == 1
    with pytest.raises(deal.OfflineContractError):
        func(True, 1)
    with pytest.raises(ZeroDivisionError):
        func(False, 0)


def test_decorating_async_function():
    @deal.raises(ZeroDivisionError)
    async def func(x):
        if x == -1:
            raise KeyError
        return 1 / x

    assert run_sync(func(1)) == 1
    with pytest.raises(ZeroDivisionError):
        run_sync(func(0))
    with pytest.raises(deal.RaisesContractError):
        run_sync(func(-1))


def test_raises_doesnt_override_another_contract_async():
    @deal.raises(ZeroDivisionError)
    @deal.has()
    async def func(do, number):
        if do:
            http = urllib3.PoolManager()
            http.request('GET', 'http://httpbin.org/robots.txt')
        return 1 / number

    assert run_sync(func(False, 1)) == 1
    with pytest.raises(deal.OfflineContractError):
        run_sync(func(True, 1))
    with pytest.raises(ZeroDivisionError):
        run_sync(func(False, 0))


def test_decorating_generator():
    @deal.raises(ZeroDivisionError)
    def func(x):
        if x == -1:
            raise KeyError
        yield 1 / x

    assert list(func(1)) == [1]
    with pytest.raises(ZeroDivisionError):
        list(func(0))
    with pytest.raises(deal.RaisesContractError):
        list(func(-1))


def test_raises_generator():
    @deal.raises(ZeroDivisionError)
    @deal.has()
    def func(do, number):
        if do:
            http = urllib3.PoolManager()
            http.request('GET', 'http://httpbin.org/robots.txt')
        yield 1 / number

    assert list(func(False, 1)) == [1]
    with pytest.raises(deal.OfflineContractError):
        list(func(True, 1))
    with pytest.raises(ZeroDivisionError):
        list(func(False, 0))
