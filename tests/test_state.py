import deal
import pytest


def test_contract_state_switch_custom_param():
    func = deal.pre(lambda x: x > 0, debug=True)(lambda x: x * 2)
    deal.switch(debug=False)
    func(-2)
    deal.switch(debug=True)
    with pytest.raises(deal.PreContractError):
        func(-2)


def test_contract_state_switch_default_param():
    func = deal.pre(lambda x: x > 0)(lambda x: x * 2)
    deal.switch(main=False)
    func(-2)
    deal.switch(main=True)
    with pytest.raises(deal.PreContractError):
        func(-2)
