import json
import sys
from pathlib import Path
from textwrap import dedent

import astroid

from deal.linter._extractors import get_exceptions
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
    returns = tuple(r.value for r in get_exceptions(body=func_tree, stubs=stubs))
    assert returns == (ZeroDivisionError, )


def test_stubs_next_to_imported_module(tmp_path: Path):
    root = tmp_path / 'project'
    root.mkdir()
    (root / '__init__.py').touch()
    (root / 'other.py').write_text('def parent(): pass')
    stub = {'parent': {'raises': ['ZeroDivisionError', 'SomeError']}}
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
        returns = tuple(r.value for r in get_exceptions(body=func_tree, stubs=stubs))
        assert set(returns) == {ZeroDivisionError, 'SomeError'}
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
    returns = tuple(r.value for r in get_exceptions(body=func_tree, stubs=stubs))
    assert returns == (TypeError, )


def test_no_stubs_for_module():
    stubs = StubsManager()

    text = """
        from astroid import parse

        @deal.raises()
        def child():
            parse()
    """
    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    func_tree = tree.body[-1].body
    returns = tuple(r.value for r in get_exceptions(body=func_tree, stubs=stubs))
    assert returns == ()


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
    returns = tuple(r.value for r in get_exceptions(body=func_tree, stubs=stubs))
    assert returns == ()


def test_marhsmallow_stubs():
    stubs = StubsManager()

    text = """
        from marshmallow.utils import from_iso_datetime

        @deal.raises()
        def child():
            return from_iso_datetime('example')
    """
    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    func_tree = tree.body[-1].body
    returns = tuple(r.value for r in get_exceptions(body=func_tree, stubs=stubs))
    assert returns == (ValueError,)
