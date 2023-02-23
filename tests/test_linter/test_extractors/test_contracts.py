import ast
from textwrap import dedent

import pytest

from deal.linter._contract import Category
from deal.linter._extractors import get_contracts
from deal.linter._extractors.contracts import SUPPORTED_CONTRACTS, SUPPORTED_MARKERS


try:
    import astroid
except ImportError:
    astroid = None


def test_supported_contracts_match_categories():
    cats = {f'deal.{c.value}' for c in Category}
    assert cats == SUPPORTED_CONTRACTS | SUPPORTED_MARKERS


def get_cats(target) -> tuple:
    return tuple(contract.name for contract in get_contracts(target))


@pytest.mark.parametrize('text, expected', [
    ('@deal.post(lambda x: x>0)', ('post', )),
    ('@deal.pure', ('pure', )),
    ('@deal.pure()', ('pure', )),
    ('@deal.chain(deal.pure)', ('pure', )),
    ('@deal.chain(deal.pure, deal.post(lambda x: x>0))', ('pure', 'post')),
])
def test_decorators(text, expected):
    text += '\ndef f(x): pass'
    if astroid is not None:
        tree = astroid.parse(text)
        assert get_cats(tree.body[-1]) == expected

    ast_tree = ast.parse(text)
    print(ast.dump(ast_tree))
    assert get_cats(ast_tree.body[-1]) == expected


@pytest.mark.skipif(astroid is None, reason='astroid is not installed')
def test_infer():
    text = """
        from io import StringIO
        import deal

        contracts = deal.chain(deal.pure, deal.post(lambda x: x>0))

        @contracts
        def f(x):
            return x

        with StringIO() as contracts2:
            @contracts2
            def f(x):
                return x
    """
    tree = astroid.parse(dedent(text))
    assert get_cats(tree.body[-2]) == ('pure', 'post')


@pytest.mark.skipif(astroid is None, reason='astroid is not installed')
def test_infer_inherit_method():
    text = """
        import deal

        class B:
            @deal.has()
            def f(self):
                pass

        class A:
            def f(self):
                pass

        class C(A, B):
            @deal.pre(lambda: True)
            def f(self):
                pass

            @deal.raises(ZeroDivisionError)
            def f2(self):
                pass

        class D(Unknown, C):
            @deal.inherit
            @deal.post(lambda x: x>0)
            def f(self):
                return 2
    """
    tree = astroid.parse(dedent(text))
    cls = tree.body[-1]
    assert isinstance(cls, astroid.ClassDef)
    assert get_cats(cls.body[0]) == ('inherit', 'pre', 'has', 'post')


@pytest.mark.skipif(astroid is None, reason='astroid is not installed')
def test_inherit_no_parents():
    text = """
        import deal
        class A:
            @deal.inherit
            @deal.has()
            def f(self):
                pass
    """
    tree = astroid.parse(dedent(text))
    cls = tree.body[-1]
    assert isinstance(cls, astroid.ClassDef)
    assert get_cats(cls.body[0]) == ('inherit', 'has')


def test_inherit_function():
    text = dedent("""
        import deal
        @deal.inherit
        def f(x):
            pass
    """)
    if astroid is not None:
        tree = astroid.parse(text)
        assert get_cats(tree.body[-1]) == ('inherit',)

    ast_tree = ast.parse(text)
    assert get_cats(ast_tree.body[-1]) == ('inherit',)
