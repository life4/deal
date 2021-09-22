import pytest
import deal


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
