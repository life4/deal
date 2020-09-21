# built-in
import ast
from pathlib import Path
from typing import Dict, Iterable, List, NamedTuple

# external
import astroid

# app
from ._contract import Category, Contract
from ._extractors import get_contracts


class Func(NamedTuple):
    name: str
    args: ast.arguments
    body: list
    contracts: Iterable[Contract]

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
        for expr in tree.body:
            if not isinstance(expr, ast.FunctionDef):
                continue
            contracts = []
            for category, args in get_contracts(expr.decorator_list):
                contract = Contract(
                    args=args,
                    category=Category(category),
                    func_args=expr.args,
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
        for expr in tree.body:
            if not isinstance(expr, astroid.FunctionDef):
                continue

            # make signature
            code = 'def f({}):0'.format(expr.args.as_string())
            func_args = ast.parse(code).body[0].args  # type: ignore

            # collect contracts
            contracts = []
            if expr.decorators:
                for category, args in get_contracts(expr.decorators.nodes):
                    contract = Contract(
                        args=args,
                        func_args=func_args,
                        category=Category(category),
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

    @staticmethod
    def _extract_defs_ast(tree: ast.Module) -> Dict[str, ast.AST]:
        result: Dict[str, ast.AST] = dict()
        for node in tree.body:
            if isinstance(node, ast.Import):
                for name_node in node.names:
                    stmt = ast.Import([name_node])
                    name = name_node.asname or name_node.name
                    result[name] = stmt
                continue

            if isinstance(node, ast.ImportFrom):
                module_name = '.' * node.level + node.module
                for name_node in node.names:
                    stmt = ast.ImportFrom(module_name, [name_node])
                    name = name_node.asname or name_node.name
                    result[name] = stmt
                continue

            if isinstance(node, ast.Expr):
                node = node.value
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if not isinstance(target, ast.Name):
                        continue
                    result[target.id] = ast.Expr(node)
        return result

    def __repr__(self) -> str:
        return '{name}({cats})'.format(
            name=type(self).__name__,
            cats=', '.join(contract.category.value for contract in self.contracts),
        )
