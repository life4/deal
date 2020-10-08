import deal
import pytest
from deal._source import get_validator_source


def test_get_validator_source():
    # autopep8: off
    c = lambda x: x > 0 # noqa
    # autopep8: on

    assert get_validator_source(c) == 'x > 0'


def test_get_validator_source_no_source():
    c = eval('lambda x: x>0')
    assert get_validator_source(c) == ''
