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
    ('raise 1 + 2', ()),
    ('assert False', (AssertionError, )),
    ('12 / 0', (ZeroDivisionError, )),
    ('12 + 0', ()),
    ('exit()', (SystemExit, )),
    ('exit(13)', (SystemExit, )),
    ('sys.exit(13)', (SystemExit, )),
    ('something.exit(13)', ()),

    # try-except
    ('try:\n raise AError\nexcept Exception:\n pass', ()),
    ('try:\n raise AError\nexcept AError:\n raise BError', ('BError', )),
    ('try:\n pass\nfinally:\n raise KeyError', (KeyError, )),

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
            c = 1 - 1
            1 / c   # implicit raise
            d = [1, 2, 3]
            1 / d   # resolved into not a constant
            a = b

        @deal.raises(KeyError)
        def f():
            a = 1
            a()         # resolved not in a function
            unknown()   # cannot resolve
            subf()      # resolve
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


def test_inference_subcontracts():
    text = """
        @deal.raises(SomeError)     # actual contract
        @deal.raises(1)             # ignore junk
        @deal.post(lambda _: 1)     # ignore other contracts
        def subf():
            return 1

        @deal.raises(KeyError)
        def f():
            b = subf()
    """
    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    func_tree = tree.body[-1].body
    returns = tuple(r.value for r in get_exceptions(body=func_tree))
    assert returns == ('SomeError', )


def test_inference_doesnt_have_exceptions():
    text = """
        def subf():
            something()
            return 1

        @deal.raises(KeyError)
        def f():
            b = subf()
    """
    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    func_tree = tree.body[-1].body
    returns = tuple(r.value for r in get_exceptions(body=func_tree))
    assert returns == ()
