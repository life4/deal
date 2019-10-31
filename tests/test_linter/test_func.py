import ast
from textwrap import dedent

import astroid

from deal.linter._func import Func


TEXT = """
import deal

@deal.post(lambda x: x > 0)
@deal.raises(ValueError, UnknownError, idk_what_is_it())
@notadeal.raises(KeyError)
@deal.notaraises(KeyError)
@something
@another.deco
@something()
def f(x):
    return x

def h(x):
    return x
"""


def test_from_text():
    funcs = Func.from_text(TEXT)
    assert len(funcs) == 2


def test_from_ast():
    funcs = Func.from_ast(ast.parse(TEXT))
    assert len(funcs) == 2


def test_from_astroid():
    funcs = Func.from_astroid(astroid.parse(TEXT))
    assert len(funcs) == 2


def test_run():
    funcs1 = Func.from_ast(ast.parse(TEXT))
    funcs2 = Func.from_astroid(astroid.parse(TEXT))
    for func in (funcs1[0], funcs2[0]):
        assert func.run(1) is True
        assert func.run(-1) is False


def test_exceptions():
    funcs1 = Func.from_ast(ast.parse(TEXT))
    funcs2 = Func.from_astroid(astroid.parse(TEXT))
    for func in (funcs1[1], funcs2[1]):
        assert func.exceptions == [ValueError, 'UnknownError']


def test_repr():
    funcs1 = Func.from_ast(ast.parse(TEXT))
    funcs2 = Func.from_astroid(astroid.parse(TEXT))
    for func in (funcs1[0], funcs2[0]):
        assert repr(func) == 'Func(post)'


def test_resolve_func():
    text = """
    import deal

    def contract(x):
        return x > 0

    @deal.post(contract)
    def f(x):
        ...
    """
    text = dedent(text).strip()
    funcs = Func.from_astroid(astroid.parse(text))
    assert len(funcs) == 1
    func = funcs[0]
    assert func.run(1) is True
    assert func.run(-1) is False


def test_resolve_lambda():
    text = """
    import deal

    contract = lambda x: x > 0

    @deal.post(contract)
    def f(x):
        ...
    """
    text = dedent(text).strip()
    funcs = Func.from_astroid(astroid.parse(text))
    assert len(funcs) == 1
    func = funcs[0]
    assert func.run(1) is True
    assert func.run(-1) is False
