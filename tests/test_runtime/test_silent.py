import sys

import pytest

import deal

from .helpers import run_sync


def test_not_allow_print():
    @deal.has()
    def func(msg):
        if msg:
            print(msg)

    func(None)
    with pytest.raises(deal.SilentContractError):
        func('bad')


def test_allow_print():
    @deal.has('stdout')
    def func(msg):
        if msg:
            print(msg)

    func(None)
    func('good')


def test_not_allow_stderr():
    @deal.has()
    def func(msg):
        if msg:
            print(msg, file=sys.stderr)

    func(None)
    with pytest.raises(deal.SilentContractError):
        func('bad')


def test_allow_stderr():
    @deal.has('stderr')
    def func(msg):
        if msg:
            print(msg, file=sys.stderr)

    func(None)
    func('good')


def test_decorating_async_function():
    @deal.has()
    async def func(msg):
        if msg:
            print(msg)
        return msg

    assert run_sync(func('')) == ''
    with pytest.raises(deal.SilentContractError):
        run_sync(func('a'))


def test_decorating_generator():
    @deal.has()
    def func(msg):
        if msg:
            print(msg)
        yield msg

    assert list(func('')) == ['']
    with pytest.raises(deal.SilentContractError):
        list(func('a'))
