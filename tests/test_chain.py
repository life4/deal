# external
import pytest
import urllib3

# project
import deal


def test_chained_contract_decorator():

    @deal.chain(deal.silent, deal.offline)
    def func(msg, do):
        if msg:
            print(msg)
        if do:
            http = urllib3.PoolManager()
            http.request('GET', 'http://httpbin.org/robots.txt')

    func(False, False)
    with pytest.raises(deal.SilentContractError):
        func(True, False)
    with pytest.raises(deal.OfflineContractError):
        func(False, True)
