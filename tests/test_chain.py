import pytest

import deal


def test_chained_contract_decorator():

    @deal.chain(
        deal.pre(lambda x: x != 1),
        deal.pre(lambda x: x != 2),
    )
    def func(x):
        return x * 4

    func(3)
    func(0)
    with pytest.raises(deal.PreContractError):
        func(1)
    with pytest.raises(deal.PreContractError):
        func(2)
