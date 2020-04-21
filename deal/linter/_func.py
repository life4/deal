# built-in
import ast
from pathlib import Path
from typing import Iterable, List

# external
import astroid

# app
from ._contract import Category, Contract
from ._extractors import get_contracts


TEMPLATE = """
contract = PLACEHOLDER
result = contract(*args, **kwargs)
"""


class Func:
    def __init__(self, body: list, contracts: Iterable[Contract]):
        self.body = body
        self.contracts = contracts

    @classmethod
    def from_path(cls, path: Path) -> List['Func']:
        text = path.read_text()
        tree = astroid.parse(code=text, path=str(path))
        return cls.from_astroid(tree)

    @classmethod
    def from_text(cls, text: str) -> List['Func']:
        tree = astroid.parse(text)
        return cls.from_astroid(tree)

    @classmethod
    def from_ast(cls, tree: ast.Module) -> List['Func']:
        funcs = []
        for expr in tree.body:
            if not isinstance(expr, ast.FunctionDef):
                continue
            contracts = []
            for category, args in get_contracts(expr.decorator_list):
                contract = Contract(args=args, category=Category(category))
                contracts.append(contract)
            if not contracts:
                continue
            funcs.append(cls(body=expr.body, contracts=contracts))
        return funcs

    @classmethod
    def from_astroid(cls, tree: astroid.Module) -> List['Func']:
        funcs = []
        for expr in tree.body:
            if not isinstance(expr, astroid.FunctionDef):
                continue
            if not expr.decorators:
                continue
            contracts = []
            for category, args in get_contracts(expr.decorators.nodes):
                contract = Contract(args=args, category=Category(category))
                contracts.append(contract)
            if not contracts:
                continue
            funcs.append(cls(body=expr.body, contracts=contracts))
        return funcs

    def __repr__(self) -> str:
        return '{name}({cats})'.format(
            name=type(self).__name__,
            cats=', '.join(contract.category.value for contract in self.contracts),
        )
