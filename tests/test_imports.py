# built-in
import ast
from pathlib import Path
from textwrap import dedent

# external
import pytest

# project
import deal
from deal._imports import DealLoader, deactivate
from deal.linter._extractors.common import get_name


def test_get_contracts():
    text = """
        import deal
        a = 1
        1 / 0
        not_a_deal.module_load(something)
        deal.module_load(deal.silent)
        """
    text = dedent(text)
    tree = ast.parse(text)
    print(ast.dump(tree))
    nodes = DealLoader._get_contracts(tree=tree)
    assert [get_name(node) for node in nodes] == ['deal.silent']


@pytest.mark.parametrize('text, expected', [
    ('deal.silent', deal.silent),
    ('deal.silent()', deal.silent),
    ('deal.pre(something)', None),
    ('not_a_deal.silent', None),
    ('deal.typo', None),
])
def test_exec_contract(text, expected):
    tree = ast.parse(text)
    print(ast.dump(tree))
    actual = DealLoader._exec_contract(node=tree.body[0].value)
    assert actual == expected


class TestException(Exception):
    pass


class TestModule:
    pass


class SubLoader:
    def __init__(self, ok, text):
        self.ok = ok
        self.text = text

    def get_source(self, module):
        assert module == 'TestModule'
        return self.text

    def exec_module(self, module):
        assert module is TestModule
        if not self.ok:
            raise TestException
        print(1)


def test_exec_module():
    text = """
        import deal
        deal.module_load(deal.silent)
        print(1)
        """
    text = dedent(text)

    with pytest.raises(TestException):
        DealLoader(loader=SubLoader(ok=False, text=text)).exec_module(TestModule)

    with pytest.raises(deal.SilentContractError):
        DealLoader(loader=SubLoader(ok=True, text=text)).exec_module(TestModule)


def test_not_path_loader():
    class SubLoaderNoGetSource:
        def exec_module(self, module):
            assert module is TestModule
            raise TestException

    with pytest.raises(TestException):
        DealLoader(loader=SubLoaderNoGetSource()).exec_module(TestModule)


def test_exec_module_invalid_contract():
    text = """
        import deal
        deal.module_load(deal.pre(something))
        print(1)
        """
    text = dedent(text)
    with pytest.raises(RuntimeError, match='unsupported contract:.+'):
        DealLoader(loader=SubLoader(ok=False, text=text)).exec_module(TestModule)


def test_exec_module_no_contracts():
    text = """
        import deal
        print(1)
        """
    text = dedent(text)
    DealLoader(loader=SubLoader(ok=True, text=text)).exec_module(TestModule)
    with pytest.raises(TestException):
        DealLoader(loader=SubLoader(ok=False, text=text)).exec_module(TestModule)


def test_exec_module_no_source():
    text = None
    DealLoader(loader=SubLoader(ok=True, text=text)).exec_module(TestModule)
    with pytest.raises(TestException):
        DealLoader(loader=SubLoader(ok=False, text=text)).exec_module(TestModule)


def test_module_load():
    assert deal.activate()
    try:
        deal.module_load(deal.silent)
    finally:
        assert deactivate()

    with pytest.raises(RuntimeError):
        deal.module_load(deal.silent)


def test_module_load_no_contracts():
    with pytest.raises(RuntimeError):
        deal.module_load()


def test_activate():
    try:
        assert deal.activate()
        assert not deal.activate()
    finally:
        assert deactivate()
        assert not deactivate()


def test_smoke():
    text = """
        import deal
        deal.module_load(deal.silent)
        print(1)
        """
    text = dedent(text)
    Path('tmp123.py').write_text(text)

    try:
        assert deal.activate()
        with pytest.raises(deal.SilentContractError):
            __import__('tmp123')
    finally:
        assert deactivate()
        assert not deactivate()
        Path('tmp123.py').unlink()
