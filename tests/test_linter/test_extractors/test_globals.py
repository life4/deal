# built-in
import ast

# external
import astroid
import pytest

# project
from deal.linter._extractors import get_globals


@pytest.mark.parametrize('text, expected', [
    ('global a', ('a', )),
    ('global a, b, c', ('a', 'b', 'c')),

    ('nonlocal a', ('a', )),
    ('nonlocal a, b, c', ('a', 'b', 'c')),

    ('import a', ('a', )),
    ('import a as b', ('a', )),
    ('import a as b, c', ('a', 'c')),
])
def test_get_globals_simple(text, expected):
    tree = astroid.parse(text)
    print(tree.repr_tree())
    globals = tuple(r.value for r in get_globals(body=tree.body))
    assert globals == expected

    tree = ast.parse(text)
    print(ast.dump(tree))
    globals = tuple(r.value for r in get_globals(body=tree.body))
    assert globals == expected
