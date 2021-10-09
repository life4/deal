import ast
from contextlib import suppress
from pathlib import Path
from textwrap import dedent

import pytest

import deal
from deal._imports import DealLoader, deactivate, get_name


@pytest.mark.parametrize('text, expected', [
    ('name', 'name'),
    ('left.right', 'left.right'),

    ('left().right', None),
    ('1', None),
])
def test_get_name(text, expected):
    tree = ast.parse(text)
    print(ast.dump(tree))
    assert isinstance(tree, ast.Module)
    expr = tree.body[0].value
    assert get_name(expr=expr) == expected


def test_get_contracts():
    text = """
        import deal
        a = 1
        1 / 0
        not_a_deal.module_load(something)
        deal.module_load(deal.pure)
        """
    text = dedent(text)
    tree = ast.parse(text)
    print(ast.dump(tree))
    nodes = DealLoader._get_contracts(tree=tree)
    assert [get_name(node) for node in nodes] == ['deal.pure']


@pytest.mark.parametrize('text, expected', [
    ('deal.pure', deal.pure),
    # ('deal.has()', deal.has),
    ('deal.pre(something)', None),
    ('not_a_deal.pure', None),
    ('deal.typo', None),
])
def test_exec_contract(text, expected):
    tree = ast.parse(text)
    print(ast.dump(tree))
    assert isinstance(tree, ast.Module)
    actual = DealLoader._exec_contract(node=tree.body[0].value)
    assert actual == expected


class FakeError(Exception):
    pass


class FakeModule:
    pass


class SubLoader:
    def __init__(self, ok, text):
        self.ok = ok
        self.text = text

    def get_source(self, module):
        assert module == 'FakeModule'
        return self.text

    def exec_module(self, module):
        assert module is FakeModule
        if not self.ok:
            raise FakeError
        print(1)


def test_exec_module():
    text = """
        import deal
        deal.module_load(deal.has())
        print(1)
        """
    text = dedent(text)

    with pytest.raises(FakeError):
        DealLoader(loader=SubLoader(ok=False, text=text)).exec_module(FakeModule)

    with pytest.raises(deal.SilentContractError):
        DealLoader(loader=SubLoader(ok=True, text=text)).exec_module(FakeModule)


def test_not_path_loader():
    class SubLoaderNoGetSource:
        def exec_module(self, module):
            assert module is FakeModule
            raise FakeError

    with pytest.raises(FakeError):
        DealLoader(loader=SubLoaderNoGetSource()).exec_module(FakeModule)


def test_exec_module_invalid_contract():
    text = """
        import deal
        deal.module_load(deal.pre(something))
        print(1)
        """
    text = dedent(text)
    with pytest.raises(RuntimeError, match='unsupported contract:.+'):
        DealLoader(loader=SubLoader(ok=False, text=text)).exec_module(FakeModule)


def test_exec_module_invalid_contract_called():
    text = """
        import deal
        deal.module_load(something())
        print(1)
        """
    text = dedent(text)
    with pytest.raises(RuntimeError, match='unsupported contract:.+'):
        DealLoader(loader=SubLoader(ok=False, text=text)).exec_module(FakeModule)


def test_exec_module_no_contracts():
    text = """
        import deal
        print(1)
        """
    text = dedent(text)
    DealLoader(loader=SubLoader(ok=True, text=text)).exec_module(FakeModule)
    with pytest.raises(FakeError):
        DealLoader(loader=SubLoader(ok=False, text=text)).exec_module(FakeModule)


def test_exec_module_no_source():
    text = None
    DealLoader(loader=SubLoader(ok=True, text=text)).exec_module(FakeModule)
    with pytest.raises(FakeError):
        DealLoader(loader=SubLoader(ok=False, text=text)).exec_module(FakeModule)


def test_module_load():
    assert deal.activate()
    try:
        deal.module_load(deal.pure)
    finally:
        assert deactivate()

    with pytest.raises(RuntimeError):
        deal.module_load(deal.pure)


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


def test_smoke_pure():
    text = """
        import deal
        deal.module_load(deal.pure)
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
        with suppress(FileNotFoundError):
            Path('tmp123.py').unlink()


def test_smoke_has():
    text = """
        import urllib3
        import deal

        deal.module_load(deal.has('stdout'))
        # stdout is ok
        print(1)

        # network is not ok
        http = urllib3.PoolManager()
        http.request('GET', 'http://httpbin.org/robots.txt')
        """
    text = dedent(text)
    Path('tmp123.py').write_text(text)

    try:
        assert deal.activate()
        with pytest.raises(deal.OfflineContractError):
            __import__('tmp123')
    finally:
        assert deactivate()
        assert not deactivate()
        Path('tmp123.py').unlink()
