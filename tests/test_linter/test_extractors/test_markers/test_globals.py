# built-in
import ast

# external
import astroid
import pytest

# project
from deal.linter._extractors import get_markers


@pytest.mark.parametrize('text, expected', [
    ('global a', ('global', )),
    ('global a, b, c', ('global', )),

    ('nonlocal a', ('global', )),
    ('nonlocal a, b, c', ('global', )),

    ('import a', ('import', )),
    ('import a as b', ('import', )),
    ('import a as b, c', ('import', )),

    ('from a import b', ('import', )),
    ('from a import b as c', ('import', )),
])
def test_get_globals_simple(text, expected):
    tree = astroid.parse(text)
    print(tree.repr_tree())
    tokens = list(get_markers(body=tree.body))
    markers = tuple(t.marker for t in tokens)
    assert markers == expected

    tree = ast.parse(text)
    print(ast.dump(tree))
    tokens = list(get_markers(body=tree.body))
    markers = tuple(t.marker for t in tokens)
    assert markers == expected
