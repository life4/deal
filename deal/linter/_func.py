import ast
from pathlib import Path
from typing import List, NamedTuple

import astroid

from ._contract import Category, Contract
from ._extractors import get_contracts, get_definitions


class Func(NamedTuple):
    name: str
    args: ast.arguments
    body: list
    contracts: List[Contract]

    line: int
    col: int

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
        definitions = get_definitions(tree=tree)
        for expr in tree.body:
            if not isinstance(expr, ast.FunctionDef):
                continue
            contracts = []
            for cinfo in get_contracts(expr):
                contract = Contract(
                    args=cinfo.args,
                    func_args=expr.args,
                    category=Category(cinfo.name),
                    context=definitions,
                    line=cinfo.line,
                )
                contracts.append(contract)
            funcs.append(cls(
                name=expr.name,
                args=expr.args,
                body=expr.body,
                contracts=contracts,
                line=expr.lineno,
                col=expr.col_offset,
            ))
        return funcs

    @classmethod
    def from_astroid(cls, tree: astroid.Module) -> List['Func']:
        funcs = []
        definitions = get_definitions(tree=tree)
        for expr in tree.body:
            if not isinstance(expr, astroid.FunctionDef):
                continue

            # make signature
            code = f'def f({expr.args.as_string()}):0'
            func_args = ast.parse(code).body[0].args  # type: ignore

            # collect contracts
            contracts = []
            for cinfo in get_contracts(expr):
                contract = Contract(
                    args=cinfo.args,
                    func_args=func_args,
                    category=Category(cinfo.name),
                    context=definitions,
                    line=cinfo.line,
                )
                contracts.append(contract)
            funcs.append(cls(
                name=expr.name,
                args=func_args,
                body=expr.body,
                contracts=contracts,
                line=expr.lineno,
                col=expr.col_offset,
            ))
        return funcs

    def __repr__(self) -> str:
        cats = ', '.join(contract.category.value for contract in self.contracts)
        return f'{type(self).__name__}({cats})'
