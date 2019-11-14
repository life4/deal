import deal
import pytest


def test_return_value_fulfils_contract():
    func = deal.post(lambda x: x > 0)(lambda x: -x)
    assert func(-4) == 4

    with pytest.raises(deal.PostContractError):
        func(4)
