import os

import pytest

import deal
import deal.introspection
from deal._imports import deactivate
from deal._state import state

from .test_runtime.helpers import run_sync


pytestmark = pytest.mark.filterwarnings("ignore:It is pytest but deal is disabled")


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


@pytest.fixture
def set_env_vars():
    old_vars = os.environ.copy()
    yield os.environ.update
    os.environ.clear()
    os.environ.update(old_vars)


@pytest.mark.parametrize('env_vars, expected', [
    (dict(), None),
    (dict(CI='true'), None),
    (dict(GCLOUD_PROJECT='example'), 'It is GCP but deal is enabled'),
    (dict(LAMBDA_TASK_ROOT='/home/'), 'It is AWS but deal is enabled'),
])
def test_enable__warnings(restore_state, env_vars, set_env_vars, expected):
    os.environ.clear()
    set_env_vars(env_vars)
    ewarn = RuntimeWarning if expected else None
    with pytest.warns(ewarn) as warns:
        deal.enable()
    if expected:
        assert len(warns) == 1
        assert str(warns[0].message) == f'{expected}. Is it intentional?'
    else:
        assert len(warns) == 0

    with pytest.warns(None) as warns:
        deal.enable(warn=False)
    assert len(warns) == 0


@pytest.mark.parametrize('env_vars, expected', [
    (dict(), None),
    (dict(GCLOUD_PROJECT='example'), None),
    (dict(LAMBDA_TASK_ROOT='/home/'), None),
    (dict(CI='true'), 'It is CI but deal is disabled'),
    (dict(PYTEST_CURRENT_TEST='test_example'), 'It is pytest but deal is disabled'),
])
def test_disable__warnings(restore_state, env_vars, set_env_vars, expected):
    os.environ.clear()
    set_env_vars(env_vars)
    ewarn = RuntimeWarning if expected else None
    with pytest.warns(ewarn) as warns:
        deal.disable()
    if expected:
        assert len(warns) == 1
        assert str(warns[0].message) == f'{expected}. Is it intentional?'
    else:
        assert len(warns) == 0

    with pytest.warns(None) as warns:
        deal.disable(warn=False)
    assert len(warns) == 0
