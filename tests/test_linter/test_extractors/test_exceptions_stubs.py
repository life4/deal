# built-in
import json
from textwrap import dedent

# external
import astroid

# project
from deal.linter._extractors import get_exceptions_stubs
from deal.linter._extractors.exceptions_stubs import _get_full_name
from deal.linter._stub import StubsManager


def test_from_stubs(tmp_path):
    root = tmp_path / 'project'
    root.mkdir()
    (root / '__init__.py').touch()
    # (root / 'other.py').touch()
    stub = {'isnan': {'raises': ['ZeroDivisionError']}}
    (root / 'math.json').write_text(json.dumps(stub))
    stubs = StubsManager(paths=[root])

    text = """
        # from project.other import parent
        from math import isnan

        @deal.raises()
        def child():
            isnan()
            # parent()
    """
    tree = astroid.parse(dedent(text))
    print(tree.repr_tree())
    func_tree = tree.body[-1].body
    returns = tuple(r.value for r in get_exceptions_stubs(body=func_tree, stubs=stubs))
    assert returns == (ZeroDivisionError, )


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
