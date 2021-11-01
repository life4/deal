import pytest

import deal


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
    contract.validate(2)
    with pytest.raises(deal.PreContractError):
        contract.validate(-1)
    assert contract.exception is deal.PreContractError
    assert contract.message is None
    assert contract.source == 'validator'


def test_unwrap():
    def validator(x):
        return x > 0

    def func(x):
        return x * 2

    wrapped = deal.pre(validator)(func)
    assert deal.introspection.unwrap(wrapped) is func
    assert deal.introspection.unwrap(func) is func


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
    assert contract.exception is deal.MarkerError
    assert contract.exception_type is deal.MarkerError
    assert contract.message is None


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


def test_init():
    @deal.pre(lambda x: x > 0)
    def func(x):
        return x * 2

    contracts = list(deal.introspection.get_contracts(func))
    assert len(contracts) == 1
    contract = contracts[0]
    assert type(contract) is deal.introspection.Pre
    val = contract._wrapped
    assert val.validate.__name__ == '_init'
    contract.init()
    assert val.validate.__name__ != '_init'
    assert val.signature


def test_init_all():
    @deal.pre(lambda x: x > 0)
    @deal.pure
    @deal.post(lambda x: x > 0)
    def func(x):
        return x * 2

    contracts = list(deal.introspection.get_contracts(func))
    assert len(contracts) == 4
    val1 = contracts[0]._wrapped
    val2 = contracts[1]._wrapped
    assert val1.validate.__name__ == '_init'
    assert val2.validate.__name__ == '_init'
    deal.introspection.init_all(func)
    assert val1.validate.__name__ != '_init'
    assert val2.validate.__name__ != '_init'
    assert val1.signature
    assert val2.signature


def test_get_contracts__inherit_class():
    class A:
        @deal.has('a', 'b')
        def f(self, x):
            raise NotImplementedError

    @deal.inherit
    class B(A):
        def f(self, x):
            return x * 2

    b = B()
    contracts = list(deal.introspection.get_contracts(b.f))
    assert len(contracts) == 1
    contract = contracts[0]
    assert isinstance(contract, deal.introspection.Has)
    assert contract.markers == frozenset({'a', 'b'})


def test_get_contracts__inherit_func():
    class A:
        @deal.has('a', 'b')
        def f(self, x):
            raise NotImplementedError

    class B(A):
        @deal.inherit
        def f(self, x):
            return x * 2

    b = B()
    contracts = list(deal.introspection.get_contracts(b.f))
    assert len(contracts) == 1
    contract = contracts[0]
    assert isinstance(contract, deal.introspection.Has)
    assert contract.markers == frozenset({'a', 'b'})
