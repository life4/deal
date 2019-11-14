import deal
import pytest
import urllib3


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
