# built-in
import json
import sys
from pathlib import Path
from textwrap import dedent

# external
import astroid

# project
from deal.linter._extractors import get_exceptions_stubs
from deal.linter._extractors.exceptions_stubs import _get_full_name
from deal.linter._stub import StubsManager


def test_stubs_in_the_root(tmp_path: Path):
    root = tmp_path / 'project'
    root.mkdir()
    (root / '__init__.py').touch()
    # (root / 'other.py').touch()
    stub = {'isnan': {'raises': ['ZeroDivisionError']}}
    (root / 'math.json').write_text(json.dumps(stub))
    stubs = StubsManager(paths=[root])

    text = """
        from math import isnan

        @deal.raises()
        def child():
            isnan()
    """
    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    func_tree = tree.body[-1].body
    returns = tuple(r.value for r in get_exceptions_stubs(body=func_tree, stubs=stubs))
    assert returns == (ZeroDivisionError, )


def test_stubs_next_to_imported_module(tmp_path: Path):
    root = tmp_path / 'project'
    root.mkdir()
    (root / '__init__.py').touch()
    (root / 'other.py').write_text('def parent(): pass')
    stub = {'parent': {'raises': ['ZeroDivisionError']}}
    (root / 'other.json').write_text(json.dumps(stub))
    stubs = StubsManager()

    text = """
        from project.other import parent

        @deal.raises()
        def child():
            parent()
    """
    sys.path.append(str(tmp_path))
    try:
        tree = astroid.parse(dedent(text))
        print(tree.repr_tree())
        func_tree = tree.body[-1].body
        returns = tuple(r.value for r in get_exceptions_stubs(body=func_tree, stubs=stubs))
        assert returns == (ZeroDivisionError, )
    finally:
        sys.path = sys.path[:-1]


def test_built_in_stubs():
    stubs = StubsManager()

    text = """
        from inspect import getfile

        @deal.raises()
        def child():
            getfile(1)
    """
    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    func_tree = tree.body[-1].body
    returns = tuple(r.value for r in get_exceptions_stubs(body=func_tree, stubs=stubs))
    assert returns == (TypeError, )


def test_infer_junk():
    stubs = StubsManager()

    text = """
        def another():
            return 2

        number = 3

        @deal.raises()
        def child():
            another()
            number()
            return unknown()  # uninferrable
    """
    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    func_tree = tree.body[-1].body
    returns = tuple(r.value for r in get_exceptions_stubs(body=func_tree, stubs=stubs))
    assert returns == ()


def test_get_full_name_func():
    tree = astroid.parse("def f(): pass")
    print(tree.repr_tree())
    func = tree.body[0]
    assert _get_full_name(expr=func) == ('', 'f')


def test_get_full_name_method():
    tree = astroid.parse("class C:\n  def f(): pass")
    print(tree.repr_tree())
    func = tree.body[0].body[0]
    assert _get_full_name(expr=func) == ('', 'C.f')


def test_get_full_name_deep_method():
    tree = astroid.parse("class A:\n  class B:\n    def f(): pass")
    print(tree.repr_tree())
    func = tree.body[0].body[0].body[0]
    assert _get_full_name(expr=func) == ('', 'A.B.f')


def test_get_full_name_func_in_func():
    tree = astroid.parse("def outer():\n def inner(): pass")
    print(tree.repr_tree())
    func = tree.body[0].body[0]
    assert _get_full_name(expr=func) == ('', 'outer.inner')


def test_get_full_name_not_a_func():
    tree = astroid.parse("try:\n pass\nexcept E as e:\n def f(): pass")
    print(tree.repr_tree())
    func = tree.body[0].handlers[0].body[0]
    assert _get_full_name(expr=func) == ('', 'f')
