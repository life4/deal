import deal
import pytest


def test_source_get_lambda_from_dec():
    @deal.pre(lambda x: x > 0)
    def f(x):
        pass

    with pytest.raises(deal.ContractError) as exc_info:
        f(-2)
    assert exc_info.value.source == 'x > 0'


def test_source_get_lambda_from_var():
    # autopep8: off
    c = lambda x: x > 0 # noqa
    # autopep8: on

    @deal.pre(c)
    def f(x):
        pass

    with pytest.raises(deal.ContractError) as exc_info:
        f(-2)
    assert exc_info.value.source == 'x > 0'


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
