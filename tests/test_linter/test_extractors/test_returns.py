# built-in
import ast

# external
import astroid
import pytest

# project
from deal.linter._extractors import get_returns


@pytest.mark.parametrize('text, expected', [
    ('return 1', (1, )),
    ('return -1', (-1, )),
    ('return 3.14', (3.14, )),
    ('return +3.14', (3.14, )),     # ignore unary plus
    ('return -3.14', (-3.14, )),    # handle unary minus
    ('return +a', ()),              # ignore uninferrable value inside of unary op
    ('return "lol"', ('lol', )),
    ('return b"lol"', (b'lol', )),
    ('return True', (True, )),
    ('return None', (None, )),

    ('if True: return 13', (13, )),
    ('if True:\n  return 13\nelse:\n  return 16', (13, 16)),
    ('for i in lst: return 13', (13, )),
    ('try:\n lol()\nexcept:\n 1\nelse:\n return 3', (3, )),
    ('try:\n lol()\nexcept:\n 1\nfinally:\n return 3', (3, )),
    ('with lol():\n return 3', (3, )),
])
def test_get_returns_simple(text, expected):
    tree = astroid.parse(text)
    print(tree.repr_tree())
    returns = tuple(r.value for r in get_returns(body=tree.body))
    assert returns == expected

    tree = ast.parse(text)
    print(ast.dump(tree))
    returns = tuple(r.value for r in get_returns(body=tree.body))
    assert returns == expected


def test_ast_uninferrable_unary():
    tree = ast.parse('return ~4')
    print(ast.dump(tree))
    returns = tuple(r.value for r in get_returns(body=tree.body))
    assert returns == ()


@pytest.mark.parametrize('text, expected', [
    ('return 1 + 2', (3, )),    # do a simple arithmetic
    ('return a', ()),           # ignore uninferrable names
    ('return ~4', (-5, )),      # handle unary bitwise NOT
])
def test_get_returns_inference(text, expected):
    tree = astroid.parse(text)
    print(tree.repr_tree())
    returns = tuple(r.value for r in get_returns(body=tree.body))
    assert returns == expected
