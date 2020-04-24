# built-in
import ast

# external
import astroid
import pytest

# project
from deal.linter._extractors import get_globals


@pytest.mark.parametrize('text, expected', [
    ('global a', ('global', )),
    ('global a, b, c', ('global', )),

    ('nonlocal a', ('nonlocal', )),
    ('nonlocal a, b, c', ('nonlocal', )),

    ('import a', ('import', )),
    ('import a as b', ('import', )),
    ('import a as b, c', ('import', )),

    ('from a import b', ('import', )),
    ('from a import b as c', ('import', )),
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
