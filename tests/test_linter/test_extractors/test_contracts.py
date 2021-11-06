import ast
from textwrap import dedent

import astroid
import pytest

from deal.linter._extractors import get_contracts


@pytest.mark.parametrize('text, expected', [
    ('@deal.post(lambda x: x>0)', ('post', )),
    ('@deal.pure', ('pure', )),
    ('@deal.pure()', ('pure', )),
    ('@deal.chain(deal.pure)', ('pure', )),
    ('@deal.chain(deal.pure, deal.post(lambda x: x>0))', ('pure', 'post')),
])
def test_get_contracts_decorators(text, expected):
    text += '\ndef f(x): pass'

    tree = astroid.parse(text)
    print(tree.repr_tree())
    decos = tree.body[-1].decorators.nodes
    returns = tuple(cat for cat, _ in get_contracts(decos))
    assert returns == expected

    tree = ast.parse(text)
    print(ast.dump(tree))
    func = tree.body[-1]
    assert isinstance(func, ast.FunctionDef)
    decos = func.decorator_list
    returns = tuple(cat for cat, _ in get_contracts(decos))
    assert returns == expected


def test_get_contracts_infer():
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
    print(tree.repr_tree())
    decos = tree.body[-2].decorators.nodes
    returns = tuple(cat for cat, _ in get_contracts(decos))
    assert returns == ('pure', 'post')


def test_get_contracts_infer_inherit_method():
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

        class D(Unknown, C):
            @deal.inherit
            @deal.post(lambda x: x>0)
            def f(self):
                return 2
    """

    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    cls = tree.body[-1]
    assert isinstance(cls, astroid.ClassDef)
    method = cls.body[0]
    assert isinstance(method, astroid.FunctionDef)
    decos = method.decorators.nodes
    returns = tuple(cat for cat, _ in get_contracts(decos))
    assert returns == ('pre', 'has', 'inherit', 'post')


def test_get_contracts_inherit_function_do_not_fail():
    text = dedent("""
        import deal

        @deal.inherit
        def f(x):
            pass
    """)

    tree = astroid.parse(text)
    print(tree.repr_tree())
    decos = tree.body[-1].decorators.nodes
    returns = tuple(cat for cat, _ in get_contracts(decos))
    assert returns == ('inherit', )

    tree = ast.parse(text)
    print(ast.dump(tree))
    func = tree.body[-1]
    assert isinstance(func, ast.FunctionDef)
    decos = func.decorator_list
    returns = tuple(cat for cat, _ in get_contracts(decos))
    assert returns == ('inherit', )
