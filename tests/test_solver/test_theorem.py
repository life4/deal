from deal._solver._theorem import Theorem, Conclusion


def prove_f(text: str) -> Theorem:
    theorems = list(Theorem.from_text(text))
    theorem = theorems[-1]
    assert theorem.name == 'f'
    assert theorem.error is None
    assert theorem.example is None
    theorem.prove()
    print('error:', theorem.error)
    print('example:', theorem.example)
    return theorem


def test_assert_true():
    theorem = prove_f("""
        def f():
            assert True
    """)
    assert theorem.conclusion is Conclusion.OK


def test_assert_false():
    theorem = prove_f("""
        def f():
            assert False
    """)
    assert theorem.conclusion is Conclusion.FAIL


def test_assert_not_equal():
    theorem = prove_f("""
        def f():
            assert 1 != 2
    """)
    assert theorem.conclusion is Conclusion.OK


def test_assert_add_int():
    theorem = prove_f("""
        def f():
            assert 1 + 2 == 3
    """)
    assert theorem.conclusion is Conclusion.OK


def test_assert_add_int_chain():
    theorem = prove_f("""
        def f():
            assert 3 + 4 + 9 == 16
    """)
    assert theorem.conclusion is Conclusion.OK


def test_assert_substract_int():
    theorem = prove_f("""
        def f():
            assert 5 - 2 == 3
    """)
    assert theorem.conclusion is Conclusion.OK


def test_assert_lt_float():
    theorem = prove_f("""
        def f():
            assert 5.1 < 5.2
    """)
    assert theorem.conclusion is Conclusion.OK


def test_assert_and_ok():
    theorem = prove_f("""
        def f():
            assert True and True
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
