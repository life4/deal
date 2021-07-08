import ast

import astroid
import pytest

from deal.linter._extractors.common import _get_module, get_full_name, get_name, infer


@pytest.mark.parametrize('text, expected', [
    ('name', 'name'),
    ('left.right', 'left.right'),

    ('left().right', None),
    ('1', None),
])
def test_get_name(text, expected):
    tree = ast.parse(text)
    print(ast.dump(tree))
    expr = tree.body[0].value
    assert get_name(expr=expr) == expected

    tree = astroid.parse(text)
    print(tree.repr_tree())
    expr = tree.body[-1].value
    assert get_name(expr=expr) == expected


@pytest.mark.parametrize('text, expected', [
    ('unknown', []),
    ('from pathlib import Path\nPath.write_text', [('pathlib', 'Path.write_text')]),
    ('def f(): pass\nf', [('', 'f')]),
    ('class C:\n def f(): pass\nC.f', [('', 'C.f')]),
    ('class C:\n def f(): pass\nc = C()\nc.f', [('', 'C.f')]),
    ('print', [('builtins', 'print')]),
    ('"".format', [('builtins', 'str.format')]),
])
def test_infer(text, expected):
    tree = astroid.parse(text)
    print(tree.repr_tree())
    expr = tree.body[-1].value
    actual = infer(expr=expr)
    assert [get_full_name(e) for e in actual] == expected


def test_get_full_name_func():
    tree = astroid.parse('def f(): pass')
    print(tree.repr_tree())
    func = tree.body[0]
    assert get_full_name(expr=func) == ('', 'f')


def test_get_full_name_method():
    tree = astroid.parse('class C:\n  def f(): pass')
    print(tree.repr_tree())
    func = tree.body[0].body[0]
    assert get_full_name(expr=func) == ('', 'C.f')


def test_get_full_name_deep_method():
    tree = astroid.parse('class A:\n  class B:\n    def f(): pass')
    print(tree.repr_tree())
    func = tree.body[0].body[0].body[0]
    assert get_full_name(expr=func) == ('', 'A.B.f')


def test_get_full_name_func_in_func():
    tree = astroid.parse('def outer():\n def inner(): pass')
    print(tree.repr_tree())
    func = tree.body[0].body[0]
    assert get_full_name(expr=func) == ('', 'outer.inner')


def test_get_full_name_not_a_func():
    tree = astroid.parse('try:\n pass\nexcept E as e:\n def f(): pass')
    print(tree.repr_tree())
    func = tree.body[0].handlers[0].body[0]
    assert get_full_name(expr=func) == ('', 'f')


def test_get_full_name_no_parent():
    tree = astroid.parse('def f(): pass')
    print(tree.repr_tree())
    assert get_full_name(expr=tree) == ('', '')


def test_get_module():
    tree = astroid.parse('def f(): pass')
    print(tree.repr_tree())
    assert _get_module(expr=tree) is tree
    assert _get_module(expr=tree.body[0]) is tree

    tree.body[0].parent = None
    assert _get_module(expr=tree.body[0]) is None
