# autopep8: off
from deal._source import get_validator_source, _extract_assignment, _extract_lambda_body, _extract_decorator_args


def test_get_validator_source():
    c = lambda x: x > 0  # noqa
    assert get_validator_source(c) == 'x > 0'


def test_get_validator_source_multiline_lambda():
    c = (lambda
        x: x > 0    # noqa: E128
        )           # noqa: E124
    assert get_validator_source(c) == 'x > 0'


def test_get_validator_source_multiple_braces():
    c = ((lambda x: x > 0))
    assert 'x > 0' in get_validator_source(c)


def test_get_validator_source_no_source():
    c = eval('lambda x: x>0')
    assert get_validator_source(c) == ''


def test_extract_assignment_no_assigment():
    assert _extract_assignment(['aragorn']) == ['aragorn']


def test_extract_lambda_body_no_lambda():
    assert _extract_lambda_body(['lambda x']) == ['lambda x']


def test_extract_decorator_args_no_call():
    assert _extract_decorator_args(['@deal.safe']) == ['@deal.safe']
