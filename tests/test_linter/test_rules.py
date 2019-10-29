import ast
from textwrap import dedent

import astroid

from deal.linter._func import Func
from deal.linter._rules import CheckRaises, CheckReturns, CheckImports


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
    text = dedent(text).strip()
    funcs1 = Func.from_ast(ast.parse(text))
    funcs2 = Func.from_astroid(astroid.parse(text))
    for func in (funcs1[0], funcs2[0]):
        actual = [tuple(err) for err in checker(func)]
        expected = [(6, 8, 'DEAL011: post contract error')]
        assert actual == expected


def test_check_raises():
    checker = CheckRaises()
    text = """
    @deal.raises(ValueError)
    def test(a):
        raise ValueError
        raise KeyError
    """
    text = dedent(text).strip()
    funcs1 = Func.from_ast(ast.parse(text))
    funcs2 = Func.from_astroid(astroid.parse(text))
    for func in (funcs1[0], funcs2[0]):
        actual = [tuple(err) for err in checker(func)]
        expected = [(4, 4, 'DEAL012: raises contract error (KeyError)')]
        assert actual == expected


def test_check_imports():
    checker = CheckImports()
    text = """
    import deal
    from deal import pre
    """
    text = dedent(text).strip()
    for tree in (ast.parse(text), astroid.parse(text)):
        actual = [tuple(err) for err in checker(tree)]
        expected = [(2, 0, 'DEAL001: ' + CheckImports.message)]
        assert actual == expected
