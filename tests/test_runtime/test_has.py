import pytest

import deal
from deal._runtime import HasPatcher

from .helpers import run_sync


def make_has(markers) -> HasPatcher:
    return HasPatcher(markers)


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
    assert make_has(markers).has_network is expected


@pytest.mark.parametrize('markers, expected', [
    (['io'], True),
    (['stdin'], True),
    (['input'], True),

    (['read'], False),
    (['write'], False),
    (['print'], False),
    (['stdout'], False),
    (['stderr'], False),
    (['unknown'], False),
])
def test_has_stdin(markers: list, expected: bool):
    assert make_has(markers).has_stdin is expected


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
    (['custom'], True),
    ([], False),
])
def test_has_io(markers: list, expected: bool):
    assert make_has(markers).has_io is expected


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
    assert make_has(markers).has_stdout is expected


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
    assert make_has(markers).has_stderr is expected


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
    assert make_has(markers).has_global is expected


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
    assert make_has(markers).has_read is expected


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
    assert make_has(markers).has_write is expected


def test_decorating_regular_function():
    @deal.has()
    def func(msg):
        if msg:
            print(msg)
        return msg

    assert func('') == ''
    with pytest.raises(deal.SilentContractError):
        func('a')


def test_custom_exception():
    @deal.has(exception=KeyError)
    def func(msg):
        if msg:
            print(msg)
        return msg

    assert func('') == ''
    with pytest.raises(KeyError):
        func('a')


def test_custom_message():
    @deal.has(message='oh hi mark')
    def func(msg):
        if msg:
            print(msg)
        return msg

    assert func('') == ''
    with pytest.raises(deal.SilentContractError, match='oh hi mark'):
        func('a')


def test_custom_exc_and_message():
    @deal.has(exception=KeyError, message='oh hi mark')
    def func(msg):
        if msg:
            print(msg)
        return msg

    assert func('') == ''
    with pytest.raises(KeyError, match='oh hi mark'):
        func('a')


def test_custom_exc_instance_and_message():
    @deal.has(exception=KeyError('oh no'), message='oh hi mark')
    def func(msg):
        if msg:
            print(msg)
        return msg

    assert func('') == ''
    with pytest.raises(KeyError, match='oh no'):
        func('a')


def test_decorating_async_function():
    @deal.has()
    async def func(msg):
        if msg:
            print(msg)
        return msg

    assert run_sync(func('')) == ''
    with pytest.raises(deal.SilentContractError):
        run_sync(func('a'))
