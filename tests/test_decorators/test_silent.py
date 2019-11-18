import deal
import pytest

from .helpers import run_sync


def test_silent_contract_not_allow_print():
    @deal.silent
    def func(msg):
        if msg:
            print(msg)

    func(None)
    with pytest.raises(deal.SilentContractError):
        func('bad')


def test_decorating_async_function():
    @deal.silent
    async def func(msg):
        if msg:
            print(msg)
        return msg

    assert run_sync(func('')) == ''
    with pytest.raises(deal.SilentContractError):
        run_sync(func('a'))


def test_decorating_generator():
    @deal.silent
    def func(msg):
        if msg:
            print(msg)
        yield msg

    assert list(func('')) == ['']
    with pytest.raises(deal.SilentContractError):
        list(func('a'))
