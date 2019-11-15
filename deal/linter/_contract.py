import ast
import builtins
import enum

import astroid

from ._extractors import get_name


TEMPLATE = """
contract = PLACEHOLDER
result = contract(*args, **kwargs)
"""


class Category(enum.Enum):
    POST = 'post'
    RAISES = 'raises'
    SILENT = 'silent'


class Contract:
    def __init__(self, args, category: Category):
        self.args = args
        self.category = category

    @property
    def body(self):
        contract = self.args[0]
        # convert astroid node to ast node
        if hasattr(contract, 'as_string'):
            contract = self._resolve_name(contract)
            contract = ast.parse(contract.as_string()).body[0]
        return contract

    @staticmethod
    def _resolve_name(contract):
        if not isinstance(contract, astroid.Name):
            return contract
        definitions = contract.lookup(contract.name)[1]
        if not definitions:
            return contract
        definition = definitions[0]
        if isinstance(definition, astroid.FunctionDef):
            return definition
        if isinstance(definition, astroid.AssignName):
            return definition.parent.value
        # resolved into something tricky, live with it
        return contract  # pragma: no cover

    @property
    def exceptions(self) -> list:
        excs = []
        for expr in self.args:
            name = get_name(expr)
            if not name:
                continue
            exc = getattr(builtins, name, name)
            excs.append(exc)
        return excs

    @property
    def bytecode(self):
        module = ast.parse(TEMPLATE)
        contract = self.body
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
