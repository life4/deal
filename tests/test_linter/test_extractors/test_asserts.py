import ast

import astroid
import pytest

from deal.linter._extractors import get_asserts


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
    tree = astroid.parse(text)
    print(tree.repr_tree())
    returns = tuple(r.value for r in get_asserts(body=tree.body))
    assert returns == expected

    tree = ast.parse(text)
    print(ast.dump(tree))
    returns = tuple(r.value for r in get_asserts(body=tree.body))
    assert returns == expected
