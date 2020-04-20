# built-in
import ast
from textwrap import dedent

# external
import astroid

# project
from deal.linter._func import Func
from deal.linter._rules import CheckImports, CheckPrints, CheckRaises, CheckReturns


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
        expected = [(6, 15, 'DEAL011: post contract error (-1)')]
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
    text = dedent(text).strip()
    funcs1 = Func.from_ast(ast.parse(text))
    funcs2 = Func.from_astroid(astroid.parse(text))
    for func in (funcs1[0], funcs2[0]):
        actual = [tuple(err) for err in checker(func)]
        expected = [(6, 15, 'DEAL011: oh no! (-1)')]
        assert actual == expected


def test_check_returns_ok_unresolved():
    checker = CheckReturns()
    text = """
    @deal.post(unknown)
    def test(a):
        return 1
    """
    text = dedent(text).strip()
    funcs1 = Func.from_ast(ast.parse(text))
    funcs2 = Func.from_astroid(astroid.parse(text))
    for func in (funcs1[0], funcs2[0]):
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
    text = dedent(text).strip()
    funcs1 = Func.from_ast(ast.parse(text))
    funcs2 = Func.from_astroid(astroid.parse(text))
    for func in (funcs1[0], funcs2[0]):
        actual = [tuple(err) for err in checker(func)]
        expected = [(4, 10, 'DEAL012: raises contract error (KeyError)')]
        assert actual == expected


def test_check_raises_without_allowed():
    checker = CheckRaises()
    text = """
    @deal.raises()
    def test(a):
        raise ValueError
    """
    text = dedent(text).strip()
    funcs1 = Func.from_ast(ast.parse(text))
    funcs2 = Func.from_astroid(astroid.parse(text))
    for func in (funcs1[0], funcs2[0]):
        actual = [tuple(err) for err in checker(func)]
        expected = [(3, 10, 'DEAL012: raises contract error (ValueError)')]
        assert actual == expected


def test_check_raises_inherited():
    checker = CheckRaises()
    text = """
    @deal.raises(LookupError)
    def test(a):
        raise KeyError
        raise ValueError
    """
    text = dedent(text).strip()
    funcs1 = Func.from_ast(ast.parse(text))
    funcs2 = Func.from_astroid(astroid.parse(text))
    for func in (funcs1[0], funcs2[0]):
        actual = [tuple(err) for err in checker(func)]
        expected = [(4, 10, 'DEAL012: raises contract error (ValueError)')]
        assert actual == expected


def test_check_prints():
    checker = CheckPrints()
    text = """
    @deal.silent
    def test(a):
        print(1)
    """
    text = dedent(text).strip()
    funcs1 = Func.from_ast(ast.parse(text))
    funcs2 = Func.from_astroid(astroid.parse(text))
    for func in (funcs1[0], funcs2[0]):
        actual = [tuple(err) for err in checker(func)]
        expected = [(3, 4, 'DEAL013: silent contract error (print)')]
        assert actual == expected


def test_check_imports():
    checker = CheckImports()
    text = """
    import deal
    from deal import pre
    from not_a_deal import pre
    from .deal import pre
    """
    text = dedent(text).strip()
    for tree in (ast.parse(text), astroid.parse(text)):
        actual = [tuple(err) for err in checker(tree)]
        expected = [(2, 0, 'DEAL001: ' + CheckImports.message)]
        assert actual == expected
