# autopep8: off
import sys
from pathlib import Path

import marshmallow
import pytest
import vaa

import deal
from deal._exceptions import _excepthook, exception_hook
from deal._state import state


def test_source_get_lambda_from_dec():
    @deal.pre(lambda x: x > 0)
    def f(x):
        pass

    with pytest.raises(deal.ContractError) as exc_info:
        f(-2)
    assert exc_info.value.source == 'x > 0'

    state.color = False
    assert str(exc_info.value) == 'expected x > 0 (where x=-2)'
    state.color = True


def test_source_get_lambda_from_dec_simple():
    @deal.pre(lambda _: _.x > 0)
    def f(x):
        pass

    with pytest.raises(deal.ContractError) as exc_info:
        f(-2)
    assert exc_info.value.source == 'x > 0'

    state.color = False
    assert str(exc_info.value) == 'expected x > 0 (where x=-2)'
    state.color = True


def test_source_get_lambda_from_var():
    c = lambda x: x > 0 # noqa

    @deal.pre(c)
    def f(x):
        pass

    with pytest.raises(deal.ContractError) as exc_info:
        f(-2)
    assert exc_info.value.source == 'x > 0'

    state.color = False
    assert str(exc_info.value) == 'expected x > 0 (where x=-2)'
    state.color = True


def test_source_get_lambda_with_braces():
    @deal.pre(lambda x: (x + 1) > (0 + 1))
    def f(x):
        pass

    with pytest.raises(deal.ContractError) as exc_info:
        f(-2)
    assert exc_info.value.source == '(x + 1) > (0 + 1)'


def test_source_get_lambda_multiline_dec():
    @deal.pre(
        lambda x: x > 0,
    )
    def f(x):
        pass

    with pytest.raises(deal.ContractError) as exc_info:
        f(-2)
    assert exc_info.value.source == 'x > 0'


def test_source_get_lambda_multiline_splitted_dec():
    @deal.pre(lambda x: x > 0 and   # noqa
                        x < 10)     # noqa
    def f(x):
        pass

    with pytest.raises(deal.ContractError) as exc_info:
        f(-2)
    assert exc_info.value.source == '<lambda>'


def test_source_get_lambda_from_many():
    @deal.pre(lambda x: x > -10)
    @deal.pre(lambda x: x > 0)
    @deal.pre(lambda x: x > -20)
    def f(x):
        pass

    with pytest.raises(deal.ContractError) as exc_info:
        f(-2)
    assert exc_info.value.source == 'x > 0'


def test_source_get_chain():
    sum_contract = deal.chain(
        deal.pre(lambda a, b: a > 0),
        deal.pre(lambda a, b: b > 0),
        deal.post(lambda res: res > 0),
    )

    @sum_contract
    def sum(a, b):
        return a + b

    with pytest.raises(deal.ContractError) as exc_info:
        sum(-2, 3)
    assert exc_info.value.source == 'a > 0'

    with pytest.raises(deal.ContractError) as exc_info:
        sum(2, -3)
    assert exc_info.value.source == 'b > 0'

    state.color = False
    assert str(exc_info.value) == 'expected b > 0 (where a=2, b=-3)'
    state.color = True


def test_source_get_func_name():
    def identity_contract(x):
        a = 0
        return x > a

    @deal.pre(identity_contract)
    def identity(x):
        return x

    with pytest.raises(deal.ContractError) as exc_info:
        identity(-2)
    assert exc_info.value.source == 'identity_contract'


def test_variables_too_long_repr():
    @deal.pre(lambda a, b: a == b)
    def f(a, b):
        return a + b

    with pytest.raises(deal.ContractError) as exc_info:
        f(234, 'x' * 60)
    state.color = False
    assert exc_info.value.variables == 'a=234'
    state.color = True


def test_source_vaa_scheme():
    class MarshMallowScheme(marshmallow.Schema):
        x = marshmallow.fields.Str()

    @deal.pre(vaa.marshmallow(MarshMallowScheme))
    def identity(x):
        return x

    with pytest.raises(deal.ContractError) as exc_info:
        identity(-2)
    assert exc_info.value.source.startswith('<vaa._external.Marshmallow object at ')
    exp = "[Error(message='Not a valid string.', field='x')] (where x=-2)"
    state.color = False
    assert str(exc_info.value) == exp
    state.color = True


def test_repr_raises_exc():
    @deal.raises()
    def identity(b):
        return 1 / b

    with pytest.raises(deal.RaisesContractError) as exc_info:
        identity(0)
    assert str(exc_info.value) == ''


def test_exception_hook(capsys):
    pre_path = str(Path('deal', '_runtime', '_contracts.py'))
    f = deal.pre(lambda x: x > 0)(lambda x: x)
    with pytest.raises(deal.PreContractError) as exc_info:
        f(-2)

    # custom hook is registered
    assert sys.excepthook is exception_hook

    # the default hook shows the full traceback
    _excepthook(exc_info.type, exc_info.value, exc_info.tb)
    captured = capsys.readouterr()
    assert captured.out == ''
    assert pre_path in captured.err

    # the custom hook hides deal from the traceback
    exception_hook(exc_info.type, exc_info.value, exc_info.tb)
    captured = capsys.readouterr()
    assert captured.out == ''
    # the hook doesn't work on python 3.6 and below
    if sys.version_info[:2] >= (3, 7):
        assert pre_path not in captured.err


def test_exception_hook_ignores_non_contract_exceptions(capsys):
    with pytest.raises(deal.NoMatchError) as exc_info:
        deal.dispatch(lambda: 0)()

    # the custom hook does not reduce non-contract tracebacks
    exception_hook(exc_info.type, exc_info.value, exc_info.tb)
    captured = capsys.readouterr()
    assert captured.out == ''
    base_path = str(Path('deal', '_runtime', '_dispatch.py'))
    assert base_path in captured.err


def test_exception_hook_ignores_contract_from_non_deal(capsys):
    with pytest.raises(deal.ContractError) as exc_info:
        raise deal.ContractError

    # the custom hook does not reduce contract from the traceback
    exception_hook(exc_info.type, exc_info.value, exc_info.tb)
    captured = capsys.readouterr()
    assert captured.out == ''
    assert 'test_exceptions.py' in captured.err


def test_custom_exc():
    @deal.pre(lambda x: x > 0, exception=ZeroDivisionError)
    def f(x):
        pass

    with pytest.raises(ZeroDivisionError) as exc_info:
        f(-2)
    assert exc_info.value.args == ()


def test_custom_exc_with_message():
    @deal.pre(lambda x: x > 0, exception=ZeroDivisionError('oh hi mark'))
    def f(x):
        pass

    with pytest.raises(ZeroDivisionError) as exc_info:
        f(-2)
    assert exc_info.value.args == ('oh hi mark',)


def test_custom_exc_and_message():
    @deal.pre(lambda x: x > 0, exception=ZeroDivisionError, message='oh hi mark')
    def f(x):
        pass

    with pytest.raises(ZeroDivisionError) as exc_info:
        f(-2)
    assert exc_info.value.args == ('oh hi mark',)


def test_custom_exc_and_returned_message():
    @deal.pre(lambda x: x > 0 or 'oh hi mark', exception=ZeroDivisionError)
    def f(x):
        pass

    with pytest.raises(ZeroDivisionError) as exc_info:
        f(-2)
    assert exc_info.value.args == ('oh hi mark',)


def test_vaa_scheme_and_custom_exception():
    @vaa.marshmallow
    class MarshMallowScheme(marshmallow.Schema):
        x = marshmallow.fields.Str()

    @deal.pre(MarshMallowScheme, exception=ZeroDivisionError)
    def identity(x):
        return x

    with pytest.raises(ZeroDivisionError) as exc_info:
        identity(-2)
    exp = "[Error(message='Not a valid string.', field='x')]"
    assert str(exc_info.value) == exp
