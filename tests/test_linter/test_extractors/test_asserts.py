# built-in
import ast

# external
import astroid
import pytest

# project
from deal.linter._extractors import get_asserts


@pytest.mark.parametrize('text, expected', [
    ('assert 1', ()),
    ('assert True', ()),
    ('assert "abc"', ()),
    ('assert "abc", "do not panic"', ()),

    ('assert 0', (0, )),
    ('assert False', (False, )),
    ('assert ""', ('', )),
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


@pytest.mark.parametrize('text, expected', [
    ('assert 3 - 2', ()),
    ('assert a', ()),           # ignore uninferrable names
    ('a = object()\nassert a', ()),

    ('assert 2 - 2', (0, )),    # do a simple arithmetic
    ('a = ""\nassert a', ('', )),
])
def test_get_asserts_inference(text, expected):
    tree = astroid.parse(text)
    print(tree.repr_tree())
    returns = tuple(r.value for r in get_asserts(body=tree.body))
    assert returns == expected
