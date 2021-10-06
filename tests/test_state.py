import pytest

import deal
from deal._imports import deactivate

from .test_runtime.helpers import run_sync


def test_contract_state_switch_custom_param():
    func = deal.pre(lambda x: x > 0)(lambda x: x * 2)
    deal.disable()
    func(-2)
    deal.enable()
    with pytest.raises(deal.PreContractError):
        func(-2)


def test_contract_state_switch_default_param():
    func = deal.pre(lambda x: x > 0)(lambda x: x * 2)
    deal.disable()
    assert func(-2) == -4
    deal.enable()
    with pytest.raises(deal.PreContractError):
        func(-2)


def test_contract_state_switch_default_param_async():
    @deal.pre(lambda x: x > 0)
    async def func(x):
        return x * 2

    deal.disable()
    assert run_sync(func(-2)) == -4
    deal.enable()
    with pytest.raises(deal.PreContractError):
        run_sync(func(-2))


def test_contract_state_switch_default_param_generator():
    @deal.pre(lambda x: x > 0)
    def func(x):
        yield x * 2

    deal.disable()
    assert list(func(-2)) == [-4]
    deal.enable()
    with pytest.raises(deal.PreContractError):
        list(func(-2))


def test_state_switch_module_load():
    with pytest.raises(RuntimeError):
        deal.module_load()
    try:
        deal.disable()
        deal.activate()
        deal.module_load()
    finally:
        deactivate()
        deal.enable()


def test_state_switch_module_load_debug():
    with pytest.raises(RuntimeError):
        deal.module_load()
    try:
        deal.disable()
        deal.activate()
        deal.enable()
    finally:
        deactivate()
        deal.reset()


def test_state_switch_activate():
    try:
        assert deal.activate()
        assert deactivate()

        deal.disable()
        assert not deal.activate()
    finally:
        deactivate()
        deal.enable()
