import deal
import pytest

from .test_decorators.helpers import run_sync


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
    assert func(-2) == -4
    deal.switch(main=True)
    with pytest.raises(deal.PreContractError):
        func(-2)


def test_contract_state_switch_default_param_async():
    @deal.pre(lambda x: x > 0)
    async def func(x):
        return x * 2

    deal.switch(main=False)
    assert run_sync(func(-2)) == -4
    deal.switch(main=True)
    with pytest.raises(deal.PreContractError):
        run_sync(func(-2))


def test_contract_state_switch_default_param_generator():
    @deal.pre(lambda x: x > 0)
    def func(x):
        yield x * 2

    deal.switch(main=False)
    assert list(func(-2)) == [-4]
    deal.switch(main=True)
    with pytest.raises(deal.PreContractError):
        list(func(-2))
