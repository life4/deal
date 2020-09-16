# built-in
import ast
import builtins
import enum
import pdb
import sys
from distutils.sysconfig import get_python_lib
from importlib.util import find_spec
from pathlib import Path

# external
import astroid


TEMPLATE = (Path(__file__).parent / '_template.py').read_text()


class Category(enum.Enum):
    HAS = 'has'
    PRE = 'pre'
    POST = 'post'
    RAISES = 'raises'
    PURE = 'pure'


class cached_property:
    def __init__(self, func):
        self.func = func

    def __get__(self, obj, cls):
        if obj is None:
            return self
        value = obj.__dict__[self.func.__name__] = self.func(obj)
        return value


class Contract:

    def __init__(self, args, category: Category, func_args: ast.arguments):
        self.args = args
        self.category = category
        self.func_args = func_args

    @cached_property
    def body(self) -> ast.AST:
        contract = self.args[0]
        # convert astroid node to ast node
        if hasattr(contract, 'as_string'):
            contract = self._resolve_name(contract)
            contract = ast.parse(contract.as_string()).body[0]
        contract = self._resolve_deps(contract)
        return contract

    @staticmethod
    def _resolve_deps(contract):
        # infer stdlib modules
        modules = set()
        stdlib_prefix = get_python_lib(standard_lib=True)
        for node in ast.walk(contract):
            if not isinstance(node, ast.Name):
                continue
            if hasattr(builtins, node.id):
                continue
            # C-compiled built-in
            if node.id in sys.builtin_module_names:
                modules.add(node.id)
                continue
            # stdlib
            spec = find_spec(node.id)
            if spec and spec.origin.startswith(stdlib_prefix):
                modules.add(node.id)
                continue

        # import inferred modules
        for module in modules:
            node: ast.Import = ast.parse('import something').body[0]
            node.names[0].name = module
            contract.body.insert(0, node)

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

    @cached_property
    def exceptions(self) -> list:
        # app
        from ._extractors import get_name

        excs = []
        for expr in self.args:
            name = get_name(expr)
            if not name:
                continue
            exc = getattr(builtins, name, name)
            excs.append(exc)
        return excs

    @cached_property
    def bytecode(self):
        module = ast.parse(TEMPLATE)

        # inject function signature
        func = ast.parse('lambda:0').body[0].value
        func.args = self.func_args
        module.body[3].value = func

        # inject contract
        contract = self.body
        if isinstance(contract, ast.FunctionDef):
            # if contract is function, add it's definition and assign it's name
            # to `contract` variable.
            module.body = [contract] + module.body
            module.body[3].value = ast.Name(
                id=contract.name,
                lineno=1,
                col_offset=1,
                ctx=ast.Load(),
            )
        else:
            if isinstance(contract, ast.Expr):
                contract = contract.value
            module.body[2].value = contract

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
