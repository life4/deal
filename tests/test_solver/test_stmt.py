# import pytest
# project
from deal._solver._theorem import Conclusion

# app
from .helpers import prove_f


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
