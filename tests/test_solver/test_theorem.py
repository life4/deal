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
