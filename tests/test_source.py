# autopep8: off
from tokenize import untokenize

from deal._source import (
    _extract_assignment, _extract_decorator_args, _extract_def_name,
    _extract_lambda_body, _get_tokens, get_validator_source, processors,
)


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
    tokens = _get_tokens(['aragorn'])
    tokens = _extract_assignment(tokens)
    text = untokenize(tokens)
    assert text == 'aragorn'


def test_extract_lambda_body_no_lambda():
    tokens = _get_tokens(['lambda x'])
    tokens = _extract_lambda_body(tokens)
    text = untokenize(tokens)
    assert text == 'lambda x'


def test_extract_decorator_args_no_call():
    tokens = _get_tokens(['@deal.safe'])
    tokens = _extract_decorator_args(tokens)
    text = untokenize(tokens)
    assert text == ' deal.safe'


def test_extract_class_name():
    tokens = _get_tokens(['class LOL', 'pass'])
    tokens = _extract_def_name(tokens)
    text = untokenize(tokens)
    assert text.lstrip() == 'LOL'


def test_no_tokens():
    assert _get_tokens([]) == []
    for processor in processors:
        assert processor([]) == []


def test_name_token():
    assert _get_tokens([]) == []
    for processor in processors:
        tokens = _get_tokens(['aragorn'])
        tokens = processor(tokens)
        text = untokenize(tokens)
        assert text == 'aragorn'
