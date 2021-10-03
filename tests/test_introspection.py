import pytest

import deal
from deal._decorators import Invariant
from deal._decorators.base import Base, StaticBase
from deal.introspection import _wrappers
from deal.introspection._extractor import WRAPPERS


def test_all_wrappers_registered():
    wrappers = set()
    for name in dir(_wrappers):
        if name.startswith('_'):
            continue
        wrapper = getattr(_wrappers, name)
        if wrapper is deal.introspection.Contract:
            continue
        if not isinstance(wrapper, type):
            continue
        if not issubclass(wrapper, deal.introspection.Contract):
            continue
        wrappers.add(wrapper)
    assert wrappers == set(WRAPPERS.values())
    assert deal.introspection.Contract not in WRAPPERS.values()


def test_all_contracts_have_wrappers():
    contracts = set(Base.__subclasses__()) | set(StaticBase.__subclasses__())
    excluded = {Invariant, StaticBase}
    assert contracts == set(WRAPPERS) | excluded


def test_usage_example():
    source = deal.introspection.__doc__.split('```python')[1].split('```')[0]
    # deal cannot extract the source code for validator if there is no source file
    source = source.replace("'x > 0'", "''")
    exec(source)


def test_get_contracts__pre():
    def validator(x):
        return x > 0

    def func(x):
        return x * 2

    wrapped = deal.pre(validator)(func)
    contracts = list(deal.introspection.get_contracts(wrapped))
    assert len(contracts) == 1
    contract = contracts[0]
    assert type(contract) is deal.introspection.Pre
    assert isinstance(contract, deal.introspection.Pre)
    assert contract.function is func
    contract.validate(2)
    with pytest.raises(deal.PreContractError):
        contract.validate(-1)
    assert contract.exception is deal.PreContractError
    assert contract.message is None
    assert contract.source == 'validator'


def test_custom_exception_and_message():
    @deal.pre(lambda x: x > 0, exception=ValueError, message='msg')
    def func(x):
        return x * 2

    contract = next(deal.introspection.get_contracts(func))
    assert isinstance(contract, deal.introspection.Pre)
    assert type(contract.exception) is ValueError
    assert contract.message == 'msg'


def test_get_contracts__raises():
    @deal.raises(ZeroDivisionError)
    def func(x):
        return x * 2

    contracts = list(deal.introspection.get_contracts(func))
    assert len(contracts) == 1
    contract = contracts[0]
    assert type(contract) is deal.introspection.Raises
    assert isinstance(contract, deal.introspection.Raises)
    assert contract.exceptions == (ZeroDivisionError,)


def test_get_contracts__reason():
    @deal.reason(ZeroDivisionError, lambda x: x > 0)
    def func(x):
        return x * 2

    contracts = list(deal.introspection.get_contracts(func))
    assert len(contracts) == 1
    contract = contracts[0]
    assert type(contract) is deal.introspection.Reason
    assert isinstance(contract, deal.introspection.Reason)
    assert contract.event == ZeroDivisionError


def test_get_contracts__has():
    @deal.has('io', 'db')
    def func(x):
        return x * 2

    contracts = list(deal.introspection.get_contracts(func))
    assert len(contracts) == 1
    contract = contracts[0]
    assert type(contract) is deal.introspection.Has
    assert isinstance(contract, deal.introspection.Has)
    assert contract.markers == frozenset({'io', 'db'})


def test_get_contracts__multiple():
    @deal.pre(lambda x: x > 0)
    @deal.post(lambda x: x >= 2)
    def func(x):
        return x * 2

    contracts = list(deal.introspection.get_contracts(func))
    assert len(contracts) == 2
    assert type(contracts[0]) is deal.introspection.Pre
    assert type(contracts[1]) is deal.introspection.Post


def test_get_contracts__example():
    @deal.example(lambda: func(3) == 6)
    def func(x):
        return x * 2

    contracts = list(deal.introspection.get_contracts(func))
    assert len(contracts) == 1
    contract = contracts[0]
    assert type(contract) is deal.introspection.Example
    assert isinstance(contract, deal.introspection.Example)
    contract.validate()
    assert contract.exception is deal.ExampleContractError
    assert contract.message is None
    assert contract.source == 'func(3) == 6'


def test_get_contracts__example_func():
    from examples.sphinx import example

    contracts = list(deal.introspection.get_contracts(example))
    assert len(contracts) == 9
