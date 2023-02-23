import ast
from textwrap import dedent
from typing import Iterator

import pytest

from deal.linter._func import Func
from deal.linter._rules import (
    CheckAsserts, CheckEnsureArgs, CheckExamples, CheckImports,
    CheckMarkers, CheckPre, CheckRaises, CheckReturns, rules,
)


try:
    import astroid
except ImportError:
    astroid = None


def get_funcs(text: str) -> Iterator:
    text = dedent(text).strip()
    funcs_ast = Func.from_ast(ast.parse(text))
    yield funcs_ast[0]
    if astroid is not None:
        funcs_astroid = Func.from_astroid(astroid.parse(text))
        yield funcs_astroid[0]


def test_error_codes():
    codes = [rule.code for rule in rules]
    assert len(codes) == len(set(codes))


def test_error_messages():
    messages = [rule.message for rule in rules]
    assert len(messages) == len(set(messages))


@pytest.mark.skipif(astroid is None, reason='astroid is not installed')
def test_check_pre():
    checker = CheckPre()
    text = """
    @deal.pre(lambda x: x > 0)
    def example(x):
        return -x

    @deal.raises()
    def caller():
        return example(-3)

    # ignore funcs without contracts
    def caller():
        return example(-3)
    """
    text = dedent(text).strip()
    funcs = Func.from_astroid(astroid.parse(text))
    assert len(funcs) == 3
    actual: list = []
    for func in funcs:
        actual.extend(tuple(err) for err in checker(func))
    expected = [(7, 11, 'DEL011 pre contract error (-3)')]
    assert actual == expected


def test_check_returns():
    checker = CheckReturns()
    text = """
    @deal.post(lambda x: x > 0)
    def test(a):
        if a:
            return 1
        else:
            return -1
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        expected = [(6, 15, 'DEL012 post contract error (-1)')]
        assert actual == expected


def test_check_returns_with_message():
    checker = CheckReturns()
    text = """
    @deal.post(lambda x: x > 0 or 'oh no!')
    def test(a):
        if a:
            return 1
        else:
            return -1
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        expected = [(6, 15, 'DEL012 oh no! (-1)')]
        assert actual == expected


def test_check_returns_ok_unresolved():
    checker = CheckReturns()
    text = """
    @deal.post(unknown)
    def test(a):
        return 1
    """
    for func in get_funcs(text):
        actual = tuple(checker(func))
        assert not actual


def test_check_raises():
    checker = CheckRaises()
    text = """
    @deal.raises(ValueError)
    def test(a):
        raise ValueError
        raise KeyError
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        expected = [(4, 10, 'DEL021 raises contract error (KeyError)')]
        assert actual == expected


def test_check_raises__skip_asserts():
    checker = CheckRaises()
    text = """
    @deal.pure
    def test(a):
        assert False
        raise AssertionError
    """
    for func in get_funcs(text):
        assert list(checker(func)) == []


def test_check_raises_safe():
    checker = CheckRaises()
    text = """
    @deal.safe
    def test(a):
        raise ValueError
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        expected = [(3, 10, 'DEL021 raises contract error (ValueError)')]
        assert actual == expected


def test_check_raises_pure():
    checker = CheckRaises()
    text = """
    @deal.pure
    def test(a):
        raise ValueError
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        expected = [(3, 10, 'DEL021 raises contract error (ValueError)')]
        assert actual == expected


def test_check_raises_without_allowed():
    checker = CheckRaises()
    text = """
    @deal.raises()
    def test(a):
        raise ValueError
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        expected = [(3, 10, 'DEL021 raises contract error (ValueError)')]
        assert actual == expected


def test_check_raises_unknown():
    checker = CheckRaises()
    text = """
    @deal.raises()
    def test(a):
        raise UnknownError
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        expected = [(3, 10, 'DEL021 raises contract error (UnknownError)')]
        assert actual == expected


def test_check_raises_inherited():
    checker = CheckRaises()
    text = """
    @deal.raises(LookupError)
    def test(a):
        raise KeyError
        raise ValueError
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        expected = [(4, 10, 'DEL021 raises contract error (ValueError)')]
        assert actual == expected


def test_check_prints():
    checker = CheckMarkers()
    text = """
    @deal.pure
    def test(a):
        print(1)
        return 1
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        expected = [(3, 4, 'DEL046 missed marker (stdout)')]
        assert actual == expected


def test_check_pure():
    checker = CheckMarkers()
    text = """
    @deal.pure
    @deal.post(lambda x: x)  # skip other contracts
    def test(a):
        global b
        return b
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        expected = [(4, 4, 'DEL041 missed marker (global)')]
        assert actual == expected


def test_check_pure_no_returns():
    checker = CheckMarkers()
    text = """
    @deal.pure
    def test(a):
        a + 3
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        assert len(actual) == 1
        expected = 'DEL043 missed marker (io)'
        assert actual[0][2] == expected


def test_check_has_io():
    checker = CheckMarkers()
    text = """
    @deal.pre(lambda a: len(a) > 2)
    @deal.has('io', 13)
    @deal.post(lambda result: result is not None)
    def test(a):
        import sys
        sys.stdout.write(a)
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        assert len(actual) == 1
        expected = 'DEL042 missed marker (import)'
        assert actual[0][2] == expected


def test_check_has_stdin():
    checker = CheckMarkers()
    text = """
    import sys

    @deal.has('stdin')
    def test(a):
        return sys.stdin.read(10)
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        assert len(actual) == 0


def test_check_has_unexpected_stdin():
    checker = CheckMarkers()
    text = """
    import sys

    @deal.has()
    def test(a):
        return sys.stdin.read(10)
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        assert len(actual) == 1
        expected = 'DEL049 missed marker (stdin)'
        assert actual[0][2] == expected


def test_check_has_unexpected_random():
    checker = CheckMarkers()
    text = """
    import random

    @deal.has()
    def test(a):
        return random.choice(a)
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        assert len(actual) == 1
        expected = 'DEL055 missed marker (random)'
        assert actual[0][2] == expected


def test_check_has_unexpected_syscall():
    checker = CheckMarkers()
    text = """
    import subprocess

    @deal.has()
    def test(a):
        return subprocess.run(a)
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        assert len(actual) == 1
        expected = 'DEL050 missed marker (syscall)'
        assert actual[0][2] == expected


@pytest.mark.skipif(astroid is None, reason='astroid is not installed')
def test_check_has_custom_markers():
    checker = CheckMarkers()
    text = """
    import deal

    @deal.has('database')
    def inner():
        return 1

    @deal.has()
    def outer():
        return inner()
    """
    text = dedent(text).strip()
    funcs = Func.from_astroid(astroid.parse(text))
    func = funcs[-1]
    actual = [tuple(err) for err in checker(func)]
    assert len(actual) == 1
    expected = 'DEL040 missed marker (database)'
    assert actual[0][2] == expected


def test_check_has_no_has():
    checker = CheckMarkers()
    text = """
    @deal.pre(lambda a: len(a) > 2)
    @deal.post(lambda result: result is not None)
    @deal.raises(ValueError)
    def test(a):
        import sys
        sys.stdout.write(a)
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        assert actual == []


def test_check_asserts():
    checker = CheckAsserts()
    text = """
    def example(a):
        assert False, "oh no!"
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        expected = [(2, 11, 'DEL031 assert error (False)')]
        assert actual == expected


def test_skip_asserts_in_tests():
    checker = CheckAsserts()
    text = """
    def test_example(a):
        assert False, "oh no!"
    """
    for func in get_funcs(text):
        actual = list(checker(func))
        assert actual == []


def test_check_imports():
    checker = CheckImports()
    text = """
    import deal
    from deal import pre
    from not_a_deal import pre
    from .deal import pre
    """
    text = dedent(text).strip()
    trees: list = [ast.parse(text)]
    if astroid is not None:
        trees.append(astroid.parse(text))
    for tree in trees:
        actual = [tuple(err) for err in checker(tree)]
        expected = [(2, 0, 'DEL001 ' + CheckImports.message)]
        assert actual == expected


def test_check_example_pre():
    checker = CheckExamples()
    text = """
    @deal.example(unknown)
    @deal.example(lambda: double(-3) == -6)
    @deal.example(lambda: unknown)
    @deal.example(unknown)
    @deal.pre(lambda a: a > 0)
    @deal.pre(lambda a: unknown)
    def double(a):
        return a * 2
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        expected = [(2, 14, 'DEL013 example violates contract (deal.pre)')]
        assert actual == expected


def test_check_example_post():
    checker = CheckExamples()
    text = """
    @deal.example(lambda: double(-3) == -6)
    @deal.example(lambda: double(3) == unknown)
    @deal.post(lambda a: a > 0)
    @deal.post(lambda a: unknown)
    def double(a):
        return a * 2
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        expected = [(1, 14, 'DEL013 example violates contract (deal.post)')]
        assert actual == expected


def test_check_example_ensure():
    checker = CheckExamples()
    text = """
    @deal.example(lambda: double(6) == 3)
    @deal.example(lambda: double(3) == unknown)
    @deal.ensure(lambda a, result: a < result)
    @deal.ensure(lambda a, result: unknown)
    def double(a):
        return a * 2
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        expected = [(1, 14, 'DEL013 example violates contract (deal.ensure)')]
        assert actual == expected


@pytest.mark.parametrize('expr, should_pass', [
    ('unknown', True),
    ('lambda a, result: 0', True),
    ('lambda a: 0', False),
])
def test_ensure_args(expr, should_pass):
    checker = CheckEnsureArgs()
    text = f"""
    @deal.ensure({expr})
    def double(a):
        return a * 2
    """
    for func in get_funcs(text):
        actual = [tuple(err) for err in checker(func)]
        if should_pass:
            assert actual == [], 'should pass but does not'
        else:
            expected = [(1, 13, 'DEL002 ensure contract must have `result` arg')]
            assert actual == expected, 'should not pass but does'
