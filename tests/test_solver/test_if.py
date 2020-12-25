from deal._solver._theorem import Conclusion
from .helpers import prove_f


def test_if_then():
    theorem = prove_f("""
        def f():
            if True:
                a = 2
            else:
                a = 3
            assert a == 2
    """)
    assert theorem.conclusion is Conclusion.OK


def test_if_else():
    theorem = prove_f("""
        def f():
            if False:
                a = 2
            else:
                a = 3
            assert a == 3
    """)
    assert theorem.conclusion is Conclusion.OK


def test_if_no_else():
    theorem = prove_f("""
        def f():
            a = 3
            if True:
                a = 2
            assert a == 2
    """)
    assert theorem.conclusion is Conclusion.OK


def test_if_else_return_from_if():
    theorem = prove_f("""
        @deal.post(lambda r: r)
        def f():
            if True:
                return True
            else:
                return False
    """)
    assert theorem.conclusion is Conclusion.OK


def test_if_else_return_from_else():
    theorem = prove_f("""
        @deal.post(lambda r: r)
        def f():
            if False:
                return False
            else:
                return True
    """)
    assert theorem.conclusion is Conclusion.OK


def test_if_return_from_if():
    theorem = prove_f("""
        @deal.post(lambda r: r)
        def f():
            if True:
                return True
            return False
    """)
    assert theorem.conclusion is Conclusion.OK


def test_if_return_after_if():
    theorem = prove_f("""
        @deal.post(lambda r: r)
        def f():
            if False:
                return False
            return True
    """)
    assert theorem.conclusion is Conclusion.OK
