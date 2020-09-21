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


@pytest.mark.parametrize('source, names', [
    ('import re', {'re'}),
    ('import typing, types', {'typing', 'types'}),
    ('import typing as types', {'types'}),

    ('from typing import List', {'List'}),
    ('from typing import List, Dict', {'List', 'Dict'}),

    ('ab = 2', {'ab'}),
    ('ab = cd = 23', {'ab', 'cd'}),
])
def test_extract_defs(source: str, names) -> None:
    tree = ast.parse(source)
    print(ast.dump(tree))
    defs = Func._extract_defs_ast(tree)
    assert set(defs) == names

    tree = astroid.parse(source)
    print(tree.repr_tree())
    defs = Func._extract_defs_astroid(tree)
    assert set(defs) == names
