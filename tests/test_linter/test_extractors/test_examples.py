import ast

import pytest

from deal.linter._extractors import get_example
from deal.linter._extractors.value import UNKNOWN


try:
    import astroid
except ImportError:
    astroid = None


@pytest.mark.parametrize('text, expected', [
    ('f(1) == 2', ([1], {}, 2)),
    ('f(1, 2) == 3', ([1, 2], {}, 3)),
    ('f(one=1) == 2', ([], {'one': 1}, 2)),
    ('f(one=1, two=2) == 3', ([], {'one': 1, 'two': 2}, 3)),
    ('f(3, 4, one=1, two=2) == 5', ([3, 4], {'one': 1, 'two': 2}, 5)),
    ('f() is None', ([], {}, None)),

    # cannot extract function result
    ('f() == abc', ([], {}, UNKNOWN)),
    ('f() < 4', ([], {}, UNKNOWN)),
    ('f() < 4 < 5', ([], {}, UNKNOWN)),

    # cannot extract example
    ('f()', None),
    ('fu() == 1', None),
    ('f(a) == 1', None),
    ('f(a=b) == 1', None),
    ('f(1)', None),
    ('f() + 4', None),
    ('hello', None),
    ('a == b', None),
    ('a == 4', None),
    ('4 == a', None),
])
def test_get_asserts_simple(text, expected):
    if astroid is not None:
        node = astroid.extract_node(text)
        print(node.repr_tree())
        result = get_example(node, func_name='f')
        assert result == expected

    ast_node = ast.parse(text).body[0]
    assert isinstance(ast_node, ast.Expr)
    print(ast.dump(ast_node))
    result = get_example(ast_node.value, func_name='f')
    assert result == expected
