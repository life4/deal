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
    '2.9 - 1.4 == 1.5',
    # '2.7 - 1.4 == 1.3',
    '2.7 > 1.4',
    '1.4 < 2.7',
    '2.7 == 2.7',

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

    # strings
    '"ab" < "cd"',
    '"ab" == "ab"',
    '"ab" != "cd"',
    '"ab" + "cd" == "abcd"',
    '"ab" + "cd" != "cdab"',
    # '"ab" * 3 == "ababab"',

    # int functions
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

    # float functions
    'int(4.2) == 4',
    # 'str(4.2) == "4.2"',

    # other expressions
    'True if True else False',
    'False if False else True',
])
def test_asserts_ok(check: str) -> None:
    assert eval(check)
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


def test_assert_and_fail():
    theorem = prove_f("""
        def f():
            assert True and False
    """)
    assert theorem.conclusion is Conclusion.FAIL
