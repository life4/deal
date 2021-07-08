import pytest

import deal

from .helpers import run_sync


@pytest.mark.parametrize('correct,incorrect', [(1, -1), (2, -2), (3, -3), (5, -5), (7, -7), (11, -11)])
def test_pre_contract_fulfilled(correct, incorrect):
    func = deal.pre(lambda x: x > 0)(lambda x: x)
    assert func(correct) == correct
    with pytest.raises(deal.PreContractError):
        func(incorrect)


@pytest.mark.parametrize('correct,incorrect_min,incorrect_max',
                         [(1, -1, 20), (2, -2, 21), (3, -3, 22), (5, -5, 23), (7, -7, 24), (9, -11, 25)])
def test_chain_all_contracts_fulfilled(correct, incorrect_min, incorrect_max):
    func = deal.pre(lambda x: x < 10)(lambda x: x)
    func = deal.pre(lambda x: x > 0)(func)
    assert func(correct) == correct
    with pytest.raises(deal.PreContractError):
        func(incorrect_min)
    with pytest.raises(deal.PreContractError):
        func(incorrect_max)


def test_correct_exceptions_raised_on_contract_fail():
    func = deal.pre(lambda x: x > 0)(lambda x: x)
    with pytest.raises(deal.PreContractError):
        func(-2)

    func = deal.pre(lambda x: x > 0, message='TEST')(lambda x: x)
    try:
        func(-2)
    except AssertionError as e:
        assert e.args[0] == 'TEST'

    func = deal.pre(lambda x: x > 0, exception=NameError)(lambda x: x)
    with pytest.raises(NameError):
        func(-2)

    func = deal.pre(lambda x: x > 0, exception=NameError('TEST'))(lambda x: x)
    with pytest.raises(NameError):
        func(-2)
    try:
        func(-2)
    except NameError as e:
        assert e.args[0] == 'TEST'

    func = deal.pre(lambda x: x > 0, message='TEST', exception=NameError)(lambda x: x)
    with pytest.raises(NameError):
        func(-2)
    try:
        func(-2)
    except NameError as e:
        assert e.args[0] == 'TEST'


def test_raise_error_with_param_on_contract_failure():
    func = deal.pre(lambda x: x > 0 or 'TEST')(lambda x: x)
    assert func(4) == 4

    with pytest.raises(deal.PreContractError):
        func(-2)

    try:
        func(-2)
    except deal.PreContractError as e:
        assert e.args[0] == 'TEST'


def test_method_decoration_name_is_correct():
    @deal.pre(lambda x: x > 0)
    def some_function(x):
        return x

    assert some_function.__name__ == 'some_function'


def test_class_method_decorator_raises_error_on_contract_fail():
    class Class:
        y = 7

        @deal.pre(lambda self, x: x > 0)
        def method(self, x):
            return x * 2

        @deal.pre(lambda self, x: x > 0)
        def method2(self, y):
            return self.y

    assert Class().method(2) == 4
    assert Class().method2(2) == 7
    with pytest.raises(deal.PreContractError):
        Class().method(-2)
    with pytest.raises(deal.PreContractError):
        Class().method2(-2)


def test_contract_returns_message():
    func = deal.pre(lambda x: x > 0 or 'TEST')(lambda x: x)
    assert func(4) == 4

    with pytest.raises(deal.PreContractError):
        func(-2)

    try:
        func(-2)
    except deal.PreContractError as e:
        assert e.args[0] == 'TEST'


def test_text_from_contract_rewrites_default_one():
    @deal.pre(lambda x: x > 0 or 'new message', message='old message')
    def double(x):
        return x * 2

    try:
        double(-1)
    except deal.PreContractError as exc:
        assert exc.args[0] == 'new message'


def test_decorating_async_function():
    @deal.pre(lambda x: x > 0)
    async def double(x):
        return x * 2

    assert run_sync(double(2)) == 4
    with pytest.raises(deal.PreContractError):
        run_sync(double(-2))


def test_decorating_generator():
    @deal.pre(lambda x: x > 0)
    def double(x):
        yield x
        yield x * 2
        yield x * 4

    assert list(double(2)) == [2, 4, 8]
    with pytest.raises(deal.PreContractError):
        list(double(-2))
