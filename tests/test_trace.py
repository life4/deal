import deal
import pytest
from deal._trace import trace, format_lines


def make_case(func) -> deal.TestCase:
    return deal.TestCase(
        args=(),
        kwargs={},
        func=func,
        exceptions=(),
        check_types=False,
    )


def just_return():
    return 123


def cond_return(cond=False):
    if cond:
        return 123
    return 456


def test_trace_100():
    case = make_case(just_return)
    result = trace(case)
    assert len(result.covered_lines) == 1
    assert len(result.all_lines) == 1
    assert result.func_result == 123


def test_trace_33():
    case = make_case(cond_return)
    result = trace(case)
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
