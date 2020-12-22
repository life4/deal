from deal._solver._theorem import Conclusion
from .helpers import prove_f


def test_call_another_no_args():
    theorem = prove_f("""
        def another() -> int:
            return 2

        def f():
            assert another() == 2
    """)
    assert theorem.conclusion is Conclusion.OK


def test_call_another_one_arg():
    theorem = prove_f("""
        def another(smth) -> int:
            return smth * 2

        def f():
            assert another(3) == 6
    """)
    assert theorem.conclusion is Conclusion.OK


def test_call_another_two_args():
    theorem = prove_f("""
        def another(a1, a2) -> int:
            return a1 - a2

        def f():
            assert another(7, 2) == 5
    """)
    assert theorem.conclusion is Conclusion.OK


def test_recursion():
    # TODO: detect infinite recursion?
    theorem = prove_f("""
        def f(a: int) -> int:
            # this is math, baby
            assert f(a) == f(a)
    """)
    assert theorem.conclusion is Conclusion.OK
