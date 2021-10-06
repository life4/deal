import pytest
import urllib3

import deal


def test_pure_silent():
    @deal.pure
    def func(msg):
        if msg:
            print(msg)

    func(None)
    with pytest.raises(deal.SilentContractError):
        func('bad')


def test_pure_safe():
    func = deal.pure(lambda x: 1 / x)
    func(2)
    with pytest.raises(deal.RaisesContractError):
        func(0)


def test_pure_offline():
    @deal.pure
    def func(do):
        if do:
            http = urllib3.PoolManager()
            http.request('GET', 'http://httpbin.org/robots.txt')

    func(False)
    with pytest.raises(deal.OfflineContractError):
        func(True)
