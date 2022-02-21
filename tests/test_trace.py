import pytest

import deal
from deal._trace import Only, _get_func_body_statements, format_lines, trace


def just_return() -> int:
    return 123


def cond_return(cond=False) -> int:
    if cond:
        return 123
    return 456


@deal.safe
@deal.has()
def cond_return_dec(cond=False) -> int:
    if cond:
        return 123
    return 456


def call_another():
    cond = something_else()
    return cond_return(cond=cond)


def something_else() -> bool:
    return False


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


def test_trace_100_exclude_everythong_else():
    result = trace(call_another)
    assert len(result.covered_lines) == 2
    assert len(result.all_lines) == 2
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


def big_test_func(cond):
    """docstring
    """
    if cond:
        return dict(
            a=1,
            b=2,
            c=3,
        )
    return 42


def test_get_func_body_statements():
    stmts = _get_func_body_statements(big_test_func)
    assert len(stmts) == 3


def test_get_func_body_statements_no_func():
    stmts = _get_func_body_statements(lambda x: x)
    assert len(stmts) == 1


def test_only():
    only = Only('excl.py')
    assert only.names('excl.py', 'anything') == 0
    assert only.names('something_else.py', 'anything') == 1
