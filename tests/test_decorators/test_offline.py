import deal
import pytest
import urllib3

from .helpers import run_sync


def test_network_request_in_offline_raises_exception():

    @deal.offline
    def func(do):
        if do:
            http = urllib3.PoolManager()
            http.request('GET', 'http://httpbin.org/robots.txt')

    func(False)
    with pytest.raises(deal.OfflineContractError):
        func(True)


def test_network_request_in_offline_and_raises_specified_exception():

    @deal.offline(exception=KeyError)
    def func(do):
        if do:
            http = urllib3.PoolManager()
            http.request('GET', 'http://httpbin.org/robots.txt')

    func(False)
    with pytest.raises(KeyError):
        func(True)


def test_decorating_async_function():
    @deal.offline
    async def func(do):
        if not do:
            return 1
        http = urllib3.PoolManager()
        http.request('GET', 'http://httpbin.org/robots.txt')

    assert run_sync(func(False)) == 1
    with pytest.raises(deal.OfflineContractError):
        run_sync(func(True))


def test_decorating_generator():
    @deal.offline
    def func(do):
        if not do:
            yield 1
            return
        http = urllib3.PoolManager()
        http.request('GET', 'http://httpbin.org/robots.txt')

    assert list(func(False)) == [1]
    with pytest.raises(deal.OfflineContractError):
        list(func(True))
