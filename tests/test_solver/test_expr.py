import math
import hypothesis
import hypothesis.strategies
import pytest
from deal._solver._theorem import Conclusion
from .helpers import prove_f


@pytest.mark.parametrize('check', [
    # logic
    'True',
    'not False',
    'True and True',
    'True or True',
    'False or True',
    'True or False',

    # math for int
    '13 == 13',
    '-13 == -13',
    '+13 == --13',
    '3 + 6 == 9',
    '7 - 4 == 3',
    '7 * 4 == 28',
    '12 / 5 == 2.4',
    '13 // 5 == 2',
    '13 % 5 == 3',
    '2 ** 3 == 8',

    # math for float
    '1.4 + 2.7 == 4.1',
    '2.9 - 1.4 == 1.5',
    # '7.0 % 3.0 == 0.5',
    # '7.0 % 3.5 == 0.0',
    '7.3 // 2.0 == 3.0',
    '2.7 > 1.4',
    '1.4 < 2.7',
    '2.7 == 2.7',
    'float("nan") != float("nan")',
    'float("inf") == float("inf")',
    '-0.0 == +0.0',

    # complex math
    '3 + 5 + 7 == 15',
    '3 * 5 * 2 == 30',
    '3 + 5 * 2 == 13',

    # comparison
    '1 != 2',
    '2 == 2',
    '3 < 4',
    '3 <= 4',
    '4 <= 4',
    '4 >= 4',
    '5 >= 4',
    '5 > 4',
    '(5 > 4) and (7 > 3)',

    # strings
    '"ab" < "cd"',
    '"ab" == "ab"',
    '"ab" != "cd"',
    '"ab" + "cd" == "abcd"',
    '"ab" + "cd" != "cdab"',
    '"bc" in "abcd"',
    # '"ab" * 3 == "ababab"',

    # int functions
    'bool(0) == False',
    'bool(1) == True',
    'bool(14) == True',
    'bool(-23) == True',
    'abs(12) == 12',
    'abs(-13) == 13',
    'min(13, 5) == 5',
    'min(5, 13) == 5',
    'max(13, 5) == 13',
    'max(5, 13) == 13',
    'float(4) == 4.0',
    'str(42) == "42"',

    # string functions
    'min("ab", "cd") == "ab"',
    'min("cd", "ab") == "ab"',
    'max("ab", "cd") == "cd"',
    'max("cd", "ab") == "cd"',
    'len("abcd") == 4',
    # 'float("12.3") == 12.3',

    # string methods
    '"abcd".startswith("ab")',
    '"abcd".endswith("cd")',
    '"abcd".index("bc") == 1',

    # float functions
    'int(4.2) == 4',
    'float("NaN") != 2.3',
    'float("Inf") > 100000',
    # 'abs(-4.2) == 4.2',
    # 'str(4.2) == "4.2"',

    # bool functions
    'int(True) == 1',
    'int(False) == 0',

    # list
    '[1, 2, 3] == [1, 2, 3]',
    '[1, 2, 3] != [1, 2, 3, 3]',
    '10 in [3, 6, 10, 17]',
    '[4, 5, 6][1] == 5',
    '[4, 5, 6, 7, 8][2:4] == [6, 7]',
    '[4, 5, 6, 7, 8][2:] == [6, 7, 8]',
    '[4, 5, 6, 7, 8][:4] == [4, 5, 6, 7]',

    # list methods
    '[7, 8, 9].index(8) == 1',

    # list functions
    'len([7, 9, 9, 9, 11]) == 5',
    'min([7, 3, 5]) == 3',
    'max([3, 7, 5]) == 7',
    'sum([3, 7, 5]) == 15',
    'sum([sum([3, 7]), 5]) == 15',

    # set
    '{1, 2, 3} == {1, 2, 3}',
    '{1, 2, 3} != {1, 2, 3, 4}',
    '{1, 2, 3} == {3, 1, 2}',
    '{1, 2, 3} == {3, 2, 1, 1, 2}',
    # 'len({7, 9, 9, 9, 11}) == 3',
    '10 in {3, 6, 10, 17}',

    # other expressions
    'True if True else False',
    'False if False else True',

    # empty sequences
    # 'len(set()) == 0',
    'len([]) == 0',
    'len("") == 0',
    'set() == set()',
    '[] == []',
    '"" == ""',

    # sequences in sequences
    'len([""]) == 1',
    'len([[]]) == 1',
    'len([[], []]) == 2',

    # converters
    'not bool(0)',
    'bool(1)',
    'bool(2)',
    'bool(-2)',
    'not bool("")',
    'bool("abc")',
    'not bool([])',
    'bool([1, 2])',
    'bool([[]])',
    'int(1) == 1',
    'int(1.5) == 1',
    'int("12") == 12',

    # implicit bool
    'not 0',
    '1',
    '1 and 3',
    '0 or 3',
    '2 if 3 else 0',
    '0 if 0 else 4',
    'not []',
    '[1, 2]',

    # comprehensions
    '[i for i in [4, 5, 6]] == [4, 5, 6]',
    '[i + i for i in [4, 5, 6]] == [8, 10, 12]',
    '[i for i in [4, 5, 6] if i != 5] == [4, 6]',
    '[i+i for i in [4, 5, 6, 7, 8] if i % 2 == 0] == [8, 12, 16]',
])
def test_asserts_ok(check: str) -> None:
    # assert eval(check)
    text = """
        from typing import List
        def f(x: List[int]):
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK


@pytest.mark.parametrize('check', [
    'False',
    'not True',
    'True and False',
    'False and True',
    'False and False',
    'False or False',
    '13 == -13',
    '3 + 6 == 10',
    'False if True else True',
    'True if False else False',
])
def test_asserts_fail(check: str) -> None:
    assert not eval(check)
    text = """
        def f():
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.FAIL


def test_lambda_one_arg():
    theorem = prove_f("""
        def f():
            a = lambda x: x * 2
            assert a(3) == 6
    """)
    assert theorem.conclusion is Conclusion.OK


def test_lambda_two_args():
    theorem = prove_f("""
        def f():
            a = lambda x, y: x - y
            assert a(7, 3) == 4
    """)
    assert theorem.conclusion is Conclusion.OK


def test_lambda_no_args():
    theorem = prove_f("""
        def f():
            a = lambda: 13
            assert a() == 13
    """)
    assert theorem.conclusion is Conclusion.OK


def test_lambda_untyped():
    theorem = prove_f("""
        def f():
            a = lambda x: x + x
            assert a(3) == 6
            assert a("ab") == "abab"
    """)
    assert theorem.conclusion is Conclusion.OK


def test_list_append():
    theorem = prove_f("""
        def f():
            a = []
            a.append(1)
            a.append(2)
            a.append(2)
            assert a == [1, 2, 2]
    """)
    assert theorem.conclusion is Conclusion.OK


def test_list_extend():
    theorem = prove_f("""
        def f():
            a = []
            a.extend([1, 2])
            a.extend([2])
            assert a == [1, 2, 2]
    """)
    assert theorem.conclusion is Conclusion.OK


@hypothesis.settings(report_multiple_bugs=False)
@hypothesis.given(
    left=hypothesis.strategies.integers(),
    right=hypothesis.strategies.integers(),
    op=hypothesis.strategies.sampled_from([
        '+', '-', '*', '/',
        '<', '<=', '==', '!=', '>=', '>',
    ]),
)
def test_fuzz_math_int(left, right, op):
    expr = '{l} {op} {r}'.format(l=left, op=op, r=right)
    expected = 0
    try:
        expected = eval(expr)
    except ZeroDivisionError:
        hypothesis.reject()

    text = """
        import math
        def f():
            assert math.isclose({expr}, {expected})
    """
    text = text.format(expr=expr, expected=expected)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK


float_strategy = hypothesis.strategies.one_of(
    hypothesis.strategies.floats(min_value=.005),
    hypothesis.strategies.floats(max_value=-.005),
)


@hypothesis.settings(report_multiple_bugs=False)
@hypothesis.given(
    left=float_strategy,
    right=float_strategy,
    op=hypothesis.strategies.sampled_from([
        '+', '-', '*', '/',
        '==', '!=', '<=', '<', '>=', '>',
    ]),
)
def test_fuzz_math_floats(left, right, op):
    expr = '{l} {op} {r}'.format(l=left, op=op, r=right)
    expected = eval(expr, {'inf': math.inf})
    if math.isinf(expected):
        hypothesis.reject()

    text = """
        import math
        def f():
            inf = float('inf')
            nan = float('nan')
            assert math.isclose({expr}, {expected})
    """
    text = text.format(expr=expr, expected=expected)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK
