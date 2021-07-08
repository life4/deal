import ast

import astroid
import pytest

from deal.linter._extractors import get_returns, has_returns


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
    ('return [1,2,3]', ([1, 2, 3], )),

    ('if True: return 13', (13, )),
    ('if True:\n  return 13\nelse:\n  return 16', (13, 16)),
    ('for i in lst: return 13', (13, )),
    ('try:\n lol()\nexcept:\n 1\nelse:\n return 3', (3, )),
    ('try:\n lol()\nexcept:\n 1\nfinally:\n return 3', (3, )),
    ('with lol():\n return 3', (3, )),

    ('yield 1', (1, )),
    ('yield -1', (-1, )),
    ('yield True', (True, )),
    ('yield a', ()),
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
    ('return 1 + 2', (3, )),                # do a simple arithmetic
    ('return a', ()),                       # ignore uninferrable names
    ('return ~4', (-5, )),                  # handle unary bitwise NOT

    ('a = 4\nreturn a', (4, )),             # infer variables
    ('a = str\nreturn a', ()),              # ignore not constants

    ('a = 4\nreturn [1, a]', ([1, 4], )),   # infer variables in list
    ('return [1, a]', ()),                  # ignore uninferralbe in list

    ('a = 4\nreturn (1, a)', ((1, 4), )),   # infer variables in set
    ('return (1, a)', ()),                  # ignore uninferralbe in set

    ('a = 4\nreturn {1, a}', ({1, 4}, )),   # infer variables in tuple
    ('return {1, a}', ()),                  # ignore uninferralbe in tuple
])
def test_get_returns_inference(text, expected):
    tree = astroid.parse(text)
    print(tree.repr_tree())
    returns = tuple(r.value for r in get_returns(body=tree.body))
    assert returns == expected


@pytest.mark.parametrize('text, expected', [
    ('return', True),
    ('return 1', True),
    ('if b:\n  return 1', True),
    ('yield 1', True),
    ('if b:\n  yield 1', True),
    ('1 + 2', False),
])
def test_has_returns(text, expected):
    tree = ast.parse(text)
    print(ast.dump(tree))
    assert has_returns(body=tree.body) is expected

    tree = astroid.parse(text)
    print(tree.repr_tree())
    assert has_returns(body=tree.body) is expected
