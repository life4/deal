import deal
import pytest
import urllib3


def test_raises_expects_function_to_raise_error():
    func = deal.raises(ZeroDivisionError)(lambda x: 1 / x)
    with pytest.raises(ZeroDivisionError):
        func(0)
    func(2)

    func = deal.raises(KeyError)(lambda x: 1 / x)
    with pytest.raises(deal.RaisesContractError):
        func(0)


def test_raises_doesnt_override_another_constract():
    @deal.raises(ZeroDivisionError)
    @deal.offline
    def func(do, number):
        if do:
            http = urllib3.PoolManager()
            http.request('GET', 'http://httpbin.org/robots.txt')
        1 / number

    func(False, 1)
    with pytest.raises(deal.OfflineContractError):
        func(True, 1)
    with pytest.raises(ZeroDivisionError):
        func(False, 0)
