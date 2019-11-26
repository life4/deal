import deal
import pytest
from deal._imports import deactivate

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


def test_state_switch_module_load():
    with pytest.raises(RuntimeError):
        deal.module_load()
    try:
        deal.switch(main=False)
        deal.activate()
        deal.module_load()
    finally:
        deactivate()
        deal.switch(main=True)


def test_state_switch_module_load_debug():
    with pytest.raises(RuntimeError):
        deal.module_load(debug=True)
    try:
        deal.switch(debug=False)
        deal.activate()
        deal.module_load(debug=True)
    finally:
        deactivate()
        deal.switch(debug=True)


def test_state_switch_activate():
    try:
        assert deal.activate()
        assert deactivate()

        deal.switch(main=False)
        assert not deal.activate()
    finally:
        deactivate()
        deal.switch(main=True)
