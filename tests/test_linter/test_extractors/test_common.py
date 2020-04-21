# built-in
import ast

# external
import astroid
import pytest

# project
from deal.linter._extractors.common import get_name


@pytest.mark.parametrize('text, expected', [
    ('name', 'name'),
    ('left.right', 'left.right'),

    ('left().right', None),
])
def test_get_name(text, expected):
    tree = ast.parse(text)
    print(ast.dump(tree))
    expr = tree.body[0].value
    assert get_name(expr=expr) == expected

    tree = astroid.parse(text)
    print(tree.repr_tree())
    expr = tree.body[0].value
    assert get_name(expr=expr) == expected
