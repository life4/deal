import deal
import pytest
from deal._trace import trace, format_lines


def just_return():
    return 123


def cond_return(cond=False):
    if cond:
        return 123
    return 456


@deal.safe
@deal.has()
def cond_return_dec(cond=False):
    if cond:
        return 123
    return 456


def test_trace_100():
    result = trace(just_return)
    assert len(result.covered_lines) == 1
    assert len(result.all_lines) == 1
    assert result.func_result == 123


def test_trace_33():
    result = trace(cond_return)
    assert len(result.covered_lines) == 2
    assert len(result.all_lines) == 3
    assert result.func_result == 456


def test_trace_33_dec():
    result = trace(cond_return_dec)
    assert len(result.covered_lines) == 2
    assert len(result.all_lines) == 3
    assert result.func_result == 456


@pytest.mark.parametrize('statements, lines, result', [
    ({1, 2, 3, 4, 5, 10, 11, 12, 13, 14}, {1, 2, 5, 10, 11, 13, 14}, '1-2, 5-11, 13-14'),
    ({1, 2, 3, 4, 5, 10, 11, 12, 13, 14, 98, 99}, {1, 2, 5, 10, 11, 13, 14, 99}, '1-2, 5-11, 13-14, 99'),
    ({1, 2, 3, 4, 98, 99, 100, 101, 102, 103, 104}, {1, 2, 99, 102, 103, 104}, '1-2, 99, 102-104'),
    ({17}, {17}, '17'),
    ({90, 91, 92, 93, 94, 95}, {90, 91, 92, 93, 94, 95}, '90-95'),
    ({1, 2, 3, 4, 5}, set(), ''),
    ({1, 2, 3, 4, 5}, {4}, '4'),
])
def test_format_lines(statements, lines, result):
    assert format_lines(statements, lines) == result
