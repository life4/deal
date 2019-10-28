import ast
import enum
from typing import List


TEMPLATE = """
contract = PLACEHOLDER
result = contract(*args, **kwargs)
"""


class Category(enum.Enum):
    PRE = 'pre'
    POST = 'post'
    RAISES = 'raises'


class Func:
    def __init__(self, body: list, contract: ast.Lambda, category: Category):
        self.body = body
        self.contract = contract
        self.category = category

    @classmethod
    def from_text(cls, text: str) -> List['Func']:
        funcs = []
        for expr in ast.parse(text).body:
            if not isinstance(expr, ast.FunctionDef):
                continue
            for contract in expr.decorator_list:
                if not isinstance(contract, ast.Call):
                    continue
                if not isinstance(contract.func, ast.Attribute):
                    continue
                if contract.func.value.id != 'deal':
                    continue
                funcs.append(cls(
                    body=expr.body,
                    category=Category(contract.func.attr),
                    contract=contract.args[0],
                ))
        return funcs

    @property
    def bytecode(self):
        module = ast.parse(TEMPLATE)
        module.body[0].value = self.contract
        return compile(module, filename='<ast>', mode='exec')

    def run(self, *args, **kwargs):
        globals = dict(args=args, kwargs=kwargs)
        exec(self.bytecode, globals)
        return globals['result']
