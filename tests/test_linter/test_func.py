# built-in
import ast

# external
import astroid
import pytest

# project
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

@something()
def k(x):
    return x
"""


def test_from_text():
    funcs = Func.from_text(TEXT)
    assert len(funcs) == 3
    assert len(funcs[0].contracts) == 2


def test_from_ast():
    funcs = Func.from_ast(ast.parse(TEXT))
    assert len(funcs) == 3
    assert len(funcs[0].contracts) == 2


def test_from_astroid():
    funcs = Func.from_astroid(astroid.parse(TEXT))
    assert len(funcs) == 3
    assert len(funcs[0].contracts) == 2


def test_repr():
    funcs1 = Func.from_ast(ast.parse(TEXT))
    funcs2 = Func.from_astroid(astroid.parse(TEXT))
    for func in (funcs1[0], funcs2[0]):
        assert repr(func) == 'Func(post, raises)'
