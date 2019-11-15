import ast
from pathlib import Path
from typing import Iterable, List

import astroid

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
            for category, args in get_contracts(expr.decorator_list):
                contract = Contract(args=args, category=Category(category))
                func = cls(
                    body=expr.body,
                    contracts=[contract],
                )
                funcs.append(func)
        return funcs

    @classmethod
    def from_astroid(cls, tree: astroid.Module) -> List['Func']:
        funcs = []
        for expr in tree.body:
            if not isinstance(expr, astroid.FunctionDef):
                continue
            if not expr.decorators:
                continue
            for category, args in get_contracts(expr.decorators.nodes):
                contract = Contract(args=args, category=Category(category))
                func = cls(
                    body=expr.body,
                    contracts=[contract],
                )
                funcs.append(func)
        return funcs

    @property
    def contract(self):
        return self.contracts[0].contract

    @property
    def exceptions(self) -> list:
        return self.contracts[0].exceptions

    @property
    def category(self) -> list:
        return self.contracts[0].category

    @property
    def bytecode(self):
        module = ast.parse(TEMPLATE)
        contract = self.contract
        if isinstance(contract, ast.FunctionDef):
            # if contract is function, add it's definition and assign it's name
            # to `contract` variable.
            module.body = [contract] + module.body
            module.body[1].value = ast.Name(
                id=contract.name,
                lineno=1,
                col_offset=1,
                ctx=ast.Load(),
            )
        else:
            if isinstance(contract, ast.Expr):
                contract = contract.value
            module.body[0].value = contract
        return compile(module, filename='<ast>', mode='exec')

    def run(self, *args, **kwargs):
        globals = dict(args=args, kwargs=kwargs)
        exec(self.bytecode, globals)
        return globals['result']

    def __repr__(self) -> str:
        return '{name}({category})'.format(
            name=type(self).__name__,
            category=self.category.value,
        )
