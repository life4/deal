import ast
import builtins
import enum
from typing import List

import astroid

from ._extractors import get_name, TOKENS


TEMPLATE = """
contract = PLACEHOLDER
result = contract(*args, **kwargs)
"""


class Category(enum.Enum):
    PRE = 'pre'
    POST = 'post'
    RAISES = 'raises'


class Func:
    def __init__(self, body: list, args, category: Category):
        self.body = body
        self.args = args
        self.category = category

    @classmethod
    def from_text(cls, text: str) -> List['Func']:
        return cls.from_astroid(astroid.parse(text))

    @classmethod
    def from_ast(cls, tree: ast.Module) -> List['Func']:
        funcs = []
        for expr in tree.body:
            if not isinstance(expr, ast.FunctionDef):
                continue
            for contract in expr.decorator_list:
                if not isinstance(contract, ast.Call):
                    continue
                if not isinstance(contract.func, ast.Attribute):
                    continue
                if not isinstance(contract.func.value, ast.Name):
                    continue
                if contract.func.value.id != 'deal':
                    continue
                funcs.append(cls(
                    body=expr.body,
                    category=Category(contract.func.attr),
                    args=contract.args,
                ))
        return funcs

    @classmethod
    def from_astroid(cls, tree: astroid.Module) -> List['Func']:
        funcs = []
        print(tree.repr_tree())
        for expr in tree.body:
            if not isinstance(expr, astroid.FunctionDef):
                continue
            for contract in expr.decorators.nodes:
                if not isinstance(contract, astroid.Call):
                    continue
                if not isinstance(contract.func, astroid.Attribute):
                    continue
                if not isinstance(contract.func.expr, astroid.Name):
                    continue
                if contract.func.expr.name != 'deal':
                    continue
                funcs.append(cls(
                    body=expr.body,
                    category=Category(contract.func.attrname),
                    args=contract.args,
                ))
        return funcs

    @property
    def contract(self):
        contract = self.args[0]
        # convert astroid node to ast node
        if hasattr(contract, 'as_string'):
            contract = ast.parse(contract.as_string()).body[0].value
        return contract

    @property
    def exceptions(self):
        excs = []
        for expr in self.args:
            name = get_name(expr)
            # raise instance
            if not name and isinstance(expr.exc, TOKENS.CALL):
                name = get_name(expr.exc.func)
                if not name or name[0].islower():
                    continue
            exc = getattr(builtins, name, name)
            excs.append(exc)
        return excs

    @property
    def bytecode(self):
        module = ast.parse(TEMPLATE)
        module.body[0].value = self.contract
        return compile(module, filename='<ast>', mode='exec')

    def run(self, *args, **kwargs):
        globals = dict(args=args, kwargs=kwargs)
        exec(self.bytecode, globals)
        return globals['result']

    def __repr__(self):
        return '{name}({category}, {contract})'.format(
            name=type(self).__name__,
            contract=ast.dump(self.contract),
            category=self.category.name,
        )
