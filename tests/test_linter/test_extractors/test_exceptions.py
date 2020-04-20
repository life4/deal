# built-in
import ast
from textwrap import dedent

# external
import astroid
import pytest

# project
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
            raise ValueError  # explicit raise

        def subf2():
            1 / 0  # implicit raise
            a = b

        @deal.raises(KeyError)
        def f():
            a = 1
            a()  # resolved not in a function
            unknown()  # cannot resolve
            subf()  # resolve
            subf2()
    """
    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    func_tree = tree.body[-1].body
    returns = tuple(r.value for r in get_exceptions(body=func_tree))
    assert returns == (ValueError, ZeroDivisionError)


def test_inference_assign():
    text = """
        def subf():
            raise Unknown

        @deal.raises(KeyError)
        def f():
            b = subf()
    """
    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    func_tree = tree.body[-1].body
    returns = tuple(r.value for r in get_exceptions(body=func_tree))
    assert returns == ('Unknown', )


def test_inference_ok_uncalled():
    text = """
        def subf():
            raise ValueError

        @deal.raises(KeyError)
        def f():
            subf
    """
    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    func_tree = tree.body[-1].body
    returns = tuple(r.value for r in get_exceptions(body=func_tree))
    assert returns == ()


def test_inference_subcalls():
    text = """
        def subf():
            raise ValueError

        def subf2():
            raise IndexError

        @deal.raises(KeyError)
        def f():
            other(subf(), b=subf2())
    """
    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    func_tree = tree.body[-1].body
    returns = tuple(r.value for r in get_exceptions(body=func_tree))
    assert returns == (ValueError, IndexError)


def test_resolve_doesnt_fail_for_simple_ast():
    text = """
        def subf():
            raise ValueError  # explicit raise

        @deal.raises(KeyError)
        def f():
            subf()
    """
    tree = ast.parse(dedent(text))
    print(ast.dump(tree))
    func_tree = tree.body[-1].body
    tuple(get_exceptions(body=func_tree))
