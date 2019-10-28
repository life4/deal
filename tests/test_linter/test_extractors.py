import ast

import pytest

from deal.linter._extractors import get_returns, get_exceptions


@pytest.mark.parametrize('text, expected', [
    ('return 1', (1, )),
    ('return -1', (-1, )),
    ('return 3.14', (3.14, )),
    ('return -3.14', (-3.14, )),
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
    returns = tuple(r.value for r in get_returns(body=ast.parse(text).body))
    assert returns == expected


@pytest.mark.parametrize('text, expected', [
    ('raise BaseException', (BaseException, )),
    ('raise ValueError', (ValueError, )),
    ('12 / 0', (ZeroDivisionError, )),

    ('if True: raise KeyError', (KeyError, )),
    ('for i in lst: raise KeyError', (KeyError, )),
])
def test_get_exceptions_simple(text, expected):
    tree = ast.parse(text)
    print(ast.dump(tree))
    returns = tuple(r.value for r in get_exceptions(body=tree.body))
    assert returns == expected
