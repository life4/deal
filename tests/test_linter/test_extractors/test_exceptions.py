import ast
from pathlib import Path
import sys
from textwrap import dedent
from typing import Dict

import astroid
import docstring_parser
import pytest

from deal.linter._extractors import get_exceptions
from deal.linter._extractors.exceptions import _excs_from_doc


@pytest.mark.parametrize('text, expected', [
    ('raise BaseException', (BaseException, )),
    ('raise ValueError', (ValueError, )),
    ('raise UnknownError', ('UnknownError', )),
    ('raise ValueError("lol")', (ValueError, )),
    ('raise unknown()', ()),
    ('raise 1 + 2', ()),
    ('raise', ()),
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
    func = tree.body[-1]
    assert isinstance(func, ast.FunctionDef)
    tuple(get_exceptions(body=func.body))


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


@pytest.fixture
def remove_import():
    old_imports: Dict[str, Dict[str, object]] = dict()

    def _remove_import(what: str):
        old_imports[what] = dict()
        for mod_name, module in sys.modules.items():
            if not mod_name.startswith('deal.'):
                continue
            if not hasattr(module, what):
                continue
            old_imports[what][mod_name] = getattr(module, what)
            setattr(module, what, None)
    yield _remove_import

    for what, imports in old_imports.items():
        for mod_name, old_import in imports.items():
            module = sys.modules[mod_name]
            setattr(module, what, old_import)


@pytest.mark.parametrize('docstring', [
    # sphinx
    pytest.param(
        """Does not raise RuntimeError.

        :raises ValueError:
        :raises KeyError: some junk
        :returns: RuntimeError
        """,
        id='sphinx',
    ),
    # epydoc
    pytest.param(
        """Does not raise RuntimeError.

        @raise ValueError:
        @raise KeyError: some junk
        @raise: something
        @return: RuntimeError
        """,
        id='epydoc',
    ),
    # google
    pytest.param(
        """Does not raise RuntimeError.

        Raises:
            ValueError:
                some junk
            KeyError: some junk
        Returns:
            RuntimeError
        """,
        id='google',
    ),
    # numpy
    pytest.param(
        """Does not raise RuntimeError.

        Raises
        ------
        ValueError
                some junk
        KeyError

        Returns
        -------
        RuntimeError
        """,
        id='numpy',
    ),
])
@pytest.mark.parametrize('patch_third_party', [True, False])
def test_extract_from_docstring(docstring, patch_third_party, remove_import):
    if patch_third_party:
        remove_import('docstring_parser')
    text = """
        def subf():
            '''{docstring}'''
            something()
            return 1

        @deal.raises(KeyError)
        def f():
            b = subf()
    """
    text = dedent(text).format(docstring=docstring)
    tree = astroid.parse(text)
    print(tree.repr_tree())
    func_tree = tree.body[-1].body
    returns = tuple(r.value for r in get_exceptions(body=func_tree))
    assert returns == (ValueError, KeyError)


def get_docstring_parser_tests():
    """Extract test cases from docstring_parser/tests.
    """
    root = Path(docstring_parser.__path__[0]) / 'tests'
    tests_found = 0
    for path in root.iterdir():
        if path.suffix != '.py':
            continue
        tree = astroid.parse(code=path.read_text(), path=str(path))
        assert isinstance(tree, astroid.Module)
        for func in tree.body:
            if not isinstance(func, astroid.FunctionDef):
                continue
            if not func.decorators:
                continue
            assert isinstance(func.decorators, astroid.Decorators)
            for dec in func.decorators.nodes:
                if not isinstance(dec, astroid.Call):
                    continue
                if dec.func.as_string() != 'pytest.mark.parametrize':
                    continue
                cases = dec.args[1]
                assert isinstance(cases, astroid.List)
                for case in cases.elts:
                    assert isinstance(case, astroid.Tuple)
                    given = case.elts[0]
                    if not isinstance(given, astroid.Const):
                        continue
                    yield pytest.param(given.value, id=f'{path.name}:{given.lineno}')
                    tests_found += 1
    assert tests_found > 10


@pytest.mark.parametrize('docstring', get_docstring_parser_tests())
def test_compare_with_docstring_parser(docstring, remove_import):
    """
    Run test cases from docstring_parser and run extractor with and without
    docstring_parser. The result must be the same.
    """
    theirs = list(_excs_from_doc(docstring))
    remove_import('docstring_parser')
    ours = list(_excs_from_doc(docstring))
    assert theirs == ours
