import deal
import pytest


def test_silent_contract_not_allow_print():
    @deal.silent
    def func(msg):
        if msg:
            print(msg)

    func(None)
    with pytest.raises(deal.SilentContractError):
        func('bad')
