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

    @something()
    def k(x):
        return x
"""


def test_from_text():
    funcs = Func.from_text(dedent(TEXT))
    assert len(funcs) == 3
    assert len(funcs[0].contracts) == 2


def test_from_ast():
    funcs = Func.from_ast(ast.parse(dedent(TEXT)))
    assert len(funcs) == 3
    assert len(funcs[0].contracts) == 2


def test_from_astroid():
    funcs = Func.from_astroid(astroid.parse(dedent(TEXT)))
    assert len(funcs) == 3
    assert len(funcs[0].contracts) == 2


def test_from_ast_methods():
    text = dedent("""
        class A:
            p = 1
            @deal.post(lambda x: x > 0)
            def f(self, x):
                return x
    """)
    funcs = Func.from_ast(ast.parse(text))
    assert len(funcs) == 1
    assert len(funcs[0].contracts) == 1


def test_from_astroid_methods():
    text = dedent("""
        class A:
            p = 1
            @deal.post(lambda x: x > 0)
            def f(self, x):
                return x
    """)
    funcs = Func.from_astroid(astroid.parse(text))
    assert len(funcs) == 1
    assert len(funcs[0].contracts) == 1


def test_repr():
    funcs1 = Func.from_ast(ast.parse(dedent(TEXT)))
    funcs2 = Func.from_astroid(astroid.parse(dedent(TEXT)))
    for func in (funcs1[0], funcs2[0]):
        assert repr(func) == 'Func(post, raises)'
