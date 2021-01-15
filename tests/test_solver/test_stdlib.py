import pytest
from deal._solver._theorem import Conclusion
from .helpers import prove_f


@pytest.mark.parametrize('check', [
    'math.isclose(5, 5)',
    'not math.isclose(5, 4)',
    'math.isclose(7.8 / 2.5, 3.12)',
    'math.isclose(2.7 - 1.4, 1.3)',

    'math.isclose(math.e, 2.718281828459045)',
    'math.isclose(math.pi, 3.141592653589793)',
    'math.isclose(math.pi/2, 1.5707963267948966)',
    'math.isclose(math.tau, 6.283185307179586)',

    'math.isinf(math.inf)',
    'math.isinf(float("inf"))',
    'math.isinf(float("-inf"))',
    'not math.isinf(123)',
    'not math.isinf(123.456)',
    'not math.isinf(float("nan"))',

    'math.isnan(math.nan)',
    'math.isnan(float("nan"))',
    'not math.isnan(123)',
    'not math.isnan(123.456)',
    'not math.isnan(float("inf"))',
    'not math.isnan(float("-inf"))',

    'math.isclose(math.sin(0), 0.0)',
    'math.isclose(math.sin(math.pi/2), 1, 1e-07)',
    'math.isclose(math.sin(-math.pi/2), -1, 1e-07)',
])
def test_math_module(check: str) -> None:
    text = """
        import math

        def f():
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK


@pytest.mark.parametrize('check', [
    'random.randint(1, 1) == 1',
    'random.randint(5, 9) > 4',
    'random.randint(5, 9) < 10',

    'random.randrange(5, 9) < 9',

    'random.choice([1]) == 1',
    'random.choice([1, 1]) == 1',
    'random.choice([1, 2, 3]) < 4',
    'random.choice([1, 2, 3]) > 0',

    # 'random.random() > -.1',
    # 'random.random() < 1.1',
])
def test_random_module(check: str) -> None:
    text = """
        import random

        def f():
            assert {}
    """
    text = text.format(check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK
