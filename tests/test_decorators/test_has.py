# external
import pytest

# project
import deal

# app
from .helpers import run_sync


@pytest.mark.parametrize('markers, expected', [
    (['io'], True),
    (['network'], True),
    (['socket'], True),
    (['network', 'stdout'], True),
    (['import', 'network', 'stdout'], True),
    (['stdout'], False),
    (['stderr'], False),
    (['write'], False),
    (['read'], False),
    (['import'], False),
])
def test_has_network(markers: list, expected: bool):
    assert deal.has(*markers).has_network is expected


@pytest.mark.parametrize('markers, expected', [
    (['io'], True),
    (['network'], True),
    (['socket'], True),
    (['network', 'stdout'], True),
    (['import', 'network', 'stdout'], True),
    (['stdout'], True),
    (['stderr'], True),
    (['write'], True),
    (['read'], True),
    (['import'], False),
    (['global'], False),
])
def test_has_io(markers: list, expected: bool):
    assert deal.has(*markers).has_io is expected


@pytest.mark.parametrize('markers, expected', [
    (['io'], True),
    (['network'], False),
    (['socket'], False),
    (['network', 'stdout'], True),
    (['import', 'network', 'stdout'], True),
    (['stdout'], True),
    (['print'], True),
    (['stderr'], False),
    (['write'], False),
    (['read'], False),
    (['import'], False),
])
def test_has_stdout(markers: list, expected: bool):
    assert deal.has(*markers).has_stdout is expected


@pytest.mark.parametrize('markers, expected', [
    (['io'], True),
    (['network'], False),
    (['socket'], False),
    (['network', 'stderr'], True),
    (['network', 'stdout'], False),
    (['import', 'network', 'stderr'], True),
    (['stderr'], True),
    (['stdout'], False),
    (['print'], False),
    (['write'], False),
    (['read'], False),
    (['import'], False),
])
def test_has_stderr(markers: list, expected: bool):
    assert deal.has(*markers).has_stderr is expected


@pytest.mark.parametrize('markers, expected', [
    (['io'], False),
    (['network'], False),
    (['socket'], False),
    (['network', 'stderr'], False),
    (['network', 'stdout'], False),
    (['import', 'network', 'stderr'], True),
    (['stderr'], False),
    (['stdout'], False),
    (['print'], False),
    (['write'], False),
    (['read'], False),
    (['import'], True),
])
def test_has_import(markers: list, expected: bool):
    assert deal.has(*markers).has_import is expected


@pytest.mark.parametrize('markers, expected', [
    (['io'], False),
    (['network'], False),
    (['socket'], False),
    (['network', 'stderr'], False),
    (['network', 'stdout'], False),
    (['import', 'global', 'stderr'], True),
    (['stderr'], False),
    (['stdout'], False),
    (['print'], False),
    (['write'], False),
    (['read'], False),
    (['import'], False),
    (['global'], True),
    (['nonlocal'], True),
])
def test_has_global(markers: list, expected: bool):
    assert deal.has(*markers).has_global is expected


@pytest.mark.parametrize('markers, expected', [
    (['io'], True),
    (['network'], False),
    (['socket'], False),
    (['network', 'stderr'], False),
    (['network', 'stdout'], False),
    (['import', 'read', 'stderr'], True),
    (['stderr'], False),
    (['stdout'], False),
    (['print'], False),
    (['write'], False),
    (['read'], True),
    (['import'], False),
    (['global'], False),
    (['nonlocal'], False),
])
def test_has_read(markers: list, expected: bool):
    assert deal.has(*markers).has_read is expected


@pytest.mark.parametrize('markers, expected', [
    (['io'], True),
    (['network'], False),
    (['socket'], False),
    (['network', 'stderr'], False),
    (['network', 'stdout'], False),
    (['import', 'write', 'stderr'], True),
    (['stderr'], False),
    (['stdout'], False),
    (['print'], False),
    (['read'], False),
    (['write'], True),
    (['import'], False),
    (['global'], False),
    (['nonlocal'], False),
])
def test_has_write(markers: list, expected: bool):
    assert deal.has(*markers).has_write is expected


def test_decorating_async_function():
    @deal.has()
    async def func(msg):
        if msg:
            print(msg)
        return msg

    assert run_sync(func('')) == ''
    with pytest.raises(deal.SilentContractError):
        run_sync(func('a'))
