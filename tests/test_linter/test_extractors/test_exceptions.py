import ast
import astroid
from textwrap import dedent

import pytest

from deal.linter._extractors import get_exceptions


@pytest.mark.parametrize('text, expected', [
    ('raise BaseException', (BaseException, )),
    ('raise ValueError', (ValueError, )),
    ('raise UnknownError', ('UnknownError', )),
    ('raise ValueError("lol")', (ValueError, )),
    ('raise unknown()', ()),
    ('assert False', (AssertionError, )),
    ('12 / 0', (ZeroDivisionError, )),
    ('exit(13)', (SystemExit, )),
    ('sys.exit(13)', (SystemExit, )),

    ('if True: raise KeyError', (KeyError, )),
    ('for i in lst: raise KeyError', (KeyError, )),
])
def test_get_exceptions_simple(text, expected):
    tree = astroid.parse(text)
    print(tree.repr_tree())
    returns = tuple(r.value for r in get_exceptions(body=tree.body))
    assert returns == expected

    tree = ast.parse(text)
    print(ast.dump(tree))
    returns = tuple(r.value for r in get_exceptions(body=tree.body))
    assert returns == expected


def test_inference_simple():
    text = """
        def subf():
            raise ValueError

        @deal.raises(KeyError)
        def f():
            subf()
    """
    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    func_tree = tree.body[-1].body
    returns = tuple(r.value for r in get_exceptions(body=func_tree))
    assert returns == (ValueError, )
