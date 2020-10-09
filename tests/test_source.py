# autopep8: off
from deal._source import get_validator_source


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
