import pytest
from deal._solver._theorem import Theorem, Conclusion


def prove_f(text: str) -> Theorem:
    theorems = list(Theorem.from_text(text))
    theorem = theorems[-1]
    assert theorem.name == 'f'
    assert theorem.error is None
    assert theorem.example is None
    theorem.prove()
    print('error:', repr(theorem.error))
    print('constraint:', repr(theorem.constraint))
    print('example:', theorem.example)
    return theorem


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
    # '12 / 5 == 2.4',
    '13 // 5 == 2',
    '13 % 5 == 3',
    '2 ** 3 == 8',

    # math for float
    '1.4 + 2.7 == 4.1',
    '2.7 - 1.4 == 1.3',

    # complex math
    '3 + 5 + 7 == 15',

    # comparison
    '1 != 2',
    '2 == 2',
    '3 < 4',
    '3 <= 4',
    '4 <= 4',
    '4 >= 4',
    '5 >= 4',
    '5 > 4',

    # other expressions
    'True if True else False',
    'False if False else True',
])
def test_asserts_ok(check: str) -> None:
    text = """
        def f():
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK


def test_assert_false():
    theorem = prove_f("""
        def f():
            assert False
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_assert_lt_float():
    theorem = prove_f("""
        def f():
            assert 5.1 < 5.2
    """)
    assert theorem.conclusion is Conclusion.OK


def test_assert_and_fail():
    theorem = prove_f("""
        def f():
            assert True and False
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_variable():
    theorem = prove_f("""
        def f():
            a = 13
            assert a == 13
            assert a != 14
            assert a == a
    """)
    assert theorem.conclusion is Conclusion.OK


def test_variable_fail():
    theorem = prove_f("""
        def f():
            a = 13
            assert a == 15
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_reassign_var():
    theorem = prove_f("""
        def f():
            a = 13
            assert a == 13
            assert a != 15

            a = 15
            assert a != 13
            assert a == 15

            b = 11
            assert a != b
            a = 11
            assert a == b
    """)
    assert theorem.conclusion is Conclusion.OK


def test_ternary_if_expr():
    theorem = prove_f("""
        def f():
            a = 13 if True else 16
            assert a == 13

            a = 13 if False else 16
            assert a == 16
    """)
    assert theorem.conclusion is Conclusion.OK


def test_unary_minus():
    theorem = prove_f("""
        def f():
            a = 13
            assert -a == -13
    """)
    assert theorem.conclusion is Conclusion.OK


def test_min_func():
    theorem = prove_f("""
        def f():
            assert min(12, 14) == 12
    """)
    assert theorem.conclusion is Conclusion.OK


def test_abs_func():
    theorem = prove_f("""
        def f():
            assert abs(12) == 12
            assert abs(-13) == 13
    """)
    assert theorem.conclusion is Conclusion.OK


def test_str_concat():
    theorem = prove_f("""
        def f():
            assert 'ab' + 'cd' == 'abcd'
            assert 'ab' + 'cd' != 'cdab'
    """)
    assert theorem.conclusion is Conclusion.OK


def test_int_single_arg():
    theorem = prove_f("""
        def f(a: int):
            assert a == a
    """)
    assert theorem.conclusion is Conclusion.OK


def test_int_two_args():
    theorem = prove_f("""
        def f(a: int, b: int):
            assert a + b == b + a
    """)
    assert theorem.conclusion is Conclusion.OK


def test_int_two_args_fail_for_some():
    theorem = prove_f("""
        def f(a: int, b: int):
            assert a != b
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_post_condition_ok():
    theorem = prove_f("""
        @deal.post(lambda result: result == 0)
        def f(a: int) -> int:
            return a - a
    """)
    assert theorem.conclusion is Conclusion.OK


def test_post_condition_fail():
    theorem = prove_f("""
        @deal.post(lambda result: result != 13)
        def f(a: int) -> int:
            return a
    """)
    assert theorem.conclusion is Conclusion.FAIL
    assert 'a = 13' in str(theorem.example)


def test_pre_condition_ok():
    theorem = prove_f("""
        @deal.pre(lambda a: a > 10)
        def f(a: int) -> int:
            assert a > 5
    """)
    assert theorem.conclusion is Conclusion.OK


def test_pre_condition_fail():
    theorem = prove_f("""
        @deal.pre(lambda a: a > 5)
        def f(a: int) -> int:
            assert a > 10
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_pre_post_condition_name_conflict():
    theorem = prove_f("""
        @deal.post(lambda a: a > 10)
        @deal.pre(lambda a: a > 5)
        @deal.pre(lambda a: a < 10)
        def f(a: int) -> int:
            return a * 2
    """)
    assert theorem.conclusion is Conclusion.OK
