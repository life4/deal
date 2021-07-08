from textwrap import dedent

import astroid

from deal.linter._extractors import get_pre


def test_check_contract():
    text = """
    @deal.pre(lambda left, right: left > right)
    def inner(left, right):
        return left + right

    def outer():
        inner(1, right=2)   # line 7
        inner(2, 3)         # line 8
        inner(2, right=1)
    """
    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    func = tree.body[-1]
    messages = [tuple(r) for r in get_pre(body=func.body)]
    assert messages == [(7, 4, '1, right=2', None), (8, 4, '2, 3', None)]


def test_cannot_infer():
    text = """
    @deal.pre(lambda left, right: something_else > left)
    def inner(left, right):
        return left + right

    def outer():
        inner(a, right=1)
        inner(1, right=a)
        inner(1, 2)
        unknown(1, right=2)
    """
    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    func = tree.body[-1]
    messages = list(get_pre(body=func.body))
    assert messages == []


def test_inferred_something_else():
    text = """
    something_else = 1

    @deal.raises(ValueError)
    def inner(a):
        return a

    def outer():
        any(1)
        inner(1)
        something_else(2)
    """
    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    func = tree.body[-1]
    messages = list(get_pre(body=func.body))
    assert messages == []
