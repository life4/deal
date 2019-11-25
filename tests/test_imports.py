import ast
from textwrap import dedent

import pytest

import deal
from deal.linter._extractors.common import get_name
from deal._imports import DealLoader


def test_get_contracts():
    text = """
        import deal
        a = 1
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
])
def test_exec_contract(text, expected):
    tree = ast.parse(text)
    print(ast.dump(tree))
    actual = DealLoader._exec_contract(node=tree.body[0].value)
    assert actual == expected


def test_exec_module():
    text = """
        import deal
        deal.module_load(deal.silent)
        print(1)
        """
    text = dedent(text)

    class TestException(Exception):
        pass

    class TestModule:
        pass

    class SubLoader:
        def __init__(self, ok):
            self.ok = ok

        def get_source(self, module):
            assert module == 'TestModule'
            return text

        def exec_module(self, module):
            assert module is TestModule
            if not self.ok:
                raise TestException
            print(1)

    with pytest.raises(TestException):
        DealLoader(loader=SubLoader(ok=False)).exec_module(TestModule)

    with pytest.raises(deal.SilentContractError):
        DealLoader(loader=SubLoader(ok=True)).exec_module(TestModule)
