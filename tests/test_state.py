import pytest

import deal
import deal.introspection
from deal._state import state
from deal._imports import deactivate

from .test_runtime.helpers import run_sync


@pytest.fixture
def restore_state():
    state.reset()
    yield
    state.removed = False
    state.reset()
    deactivate()


def count_contracts(func) -> int:
    return len(list(deal.introspection.get_contracts(func)))


def test_contract_state_switch_custom_param(restore_state):
    func = deal.pre(lambda x: x > 0)(lambda x: x * 2)
    deal.disable()
    func(-2)
    deal.enable()
    with pytest.raises(deal.PreContractError):
        func(-2)


def test_contract_state_switch_default_param(restore_state):
    func = deal.pre(lambda x: x > 0)(lambda x: x * 2)
    deal.disable()
    assert func(-2) == -4
    deal.enable()
    with pytest.raises(deal.PreContractError):
        func(-2)


def test_contract_state_switch_default_param_async(restore_state):
    @deal.pre(lambda x: x > 0)
    async def func(x):
        return x * 2

    deal.disable()
    assert run_sync(func(-2)) == -4
    deal.enable()
    with pytest.raises(deal.PreContractError):
        run_sync(func(-2))


def test_contract_state_switch_default_param_generator(restore_state):
    @deal.pre(lambda x: x > 0)
    def func(x):
        yield x * 2

    deal.disable()
    assert list(func(-2)) == [-4]
    deal.enable()
    with pytest.raises(deal.PreContractError):
        list(func(-2))


def test_state_disable_permament(restore_state):
    @deal.pre(lambda x: x > 0)
    @deal.inherit
    @deal.pure
    def func1(x):
        yield x * 2

    deal.disable(permament=True)

    @deal.pre(lambda x: x > 0)
    @deal.inherit
    @deal.pure
    def func2(x):
        yield x * 2

    assert count_contracts(func1) == 3
    assert count_contracts(func2) == 0


def test_state_disable_permament__cant_disable_twice(restore_state):
    deal.disable(permament=True)
    with pytest.raises(RuntimeError):
        deal.disable(permament=True)
    with pytest.raises(RuntimeError):
        deal.enable()
    with pytest.raises(RuntimeError):
        deal.reset()


def test_state_switch_module_load(restore_state):
    with pytest.raises(RuntimeError):
        deal.module_load()
    deal.disable()
    deal.activate()
    deal.module_load()


def test_state_switch_module_load_debug(restore_state):
    with pytest.raises(RuntimeError):
        deal.module_load()
    deal.disable()
    deal.activate()
    deal.enable()


def test_state_switch_activate(restore_state):
    assert deal.activate()
    assert deactivate()

    deal.disable()
    assert not deal.activate()
