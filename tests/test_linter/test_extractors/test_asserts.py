import ast

import pytest

from deal.linter._extractors import get_asserts


try:
    import astroid
except ImportError:
    astroid = None


@pytest.mark.parametrize('text, expected', [
    ('assert 1', ()),
    ('assert True', ()),
    ('assert "abc"', ()),
    ('assert "abc", "do not panic"', ()),

    ('assert 0', (0, )),
    ('assert False', (False, )),
    ('assert ""', ('', )),
    ('assert []', ([], )),

    ('assert 3 - 2', ()),
    # ('assert 2 - 2', (0, )),
    ('assert a', ()),           # ignore uninferrable names
    ('a = object()\nassert a', ()),
])
def test_get_asserts_simple(text, expected):
    if astroid is not None:
        tree = astroid.parse(text)
        print(tree.repr_tree())
        returns = tuple(r.value for r in get_asserts(body=tree.body))
        assert returns == expected

    ast_tree = ast.parse(text)
    print(ast.dump(ast_tree))
    returns = tuple(r.value for r in get_asserts(body=ast_tree.body))
    assert returns == expected
