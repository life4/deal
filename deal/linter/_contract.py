# built-in
import ast
import builtins
import enum
from copy import copy
from pathlib import Path
from typing import Dict, FrozenSet, Iterable

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
    args: tuple
    category: Category
    func_args: ast.arguments
    context: Dict[str, ast.AST]

    def __init__(
        self,
        args: Iterable,
        category: Category,
        func_args: ast.arguments,
        context: Dict[str, ast.AST] = None,
    ):
        self.args = tuple(args)
        self.category = category
        self.func_args = func_args
        self.context = context or dict()

    @cached_property
    def body(self) -> ast.AST:
        contract = self.args[0]
        # convert astroid node to ast node
        if hasattr(contract, 'as_string'):
            contract = self._resolve_name(contract)
            contract = ast.parse(contract.as_string()).body[0]
        return contract

    @cached_property
    def arguments(self) -> FrozenSet[str]:
        """Contract function arguments names.

        Useful for resolving external dependencies.
        """
        func = self.body
        if isinstance(func, ast.Expr):
            func = func.value
        if not isinstance(func, (ast.FunctionDef, ast.Lambda)):
            return frozenset()
        args = func.args
        result = set()
        for arg in args.args:
            result.add(arg.arg)
        for arg in args.kwonlyargs:
            result.add(arg.arg)
        if args.vararg:
            result.add(args.vararg.arg)
        if args.kwarg:
            result.add(args.kwarg.arg)
        return result

    @cached_property
    def dependencies(self) -> FrozenSet[str]:
        """Names that are defined outside of the contract body.

        1. Excludes built-in objects.
        1. Excludes contract function arguments.
        """
        deps = set()
        for node in ast.walk(self.body):
            if not isinstance(node, ast.Name):
                continue
            if hasattr(builtins, node.id):
                continue
            if node.id in self.arguments:
                continue
            deps.add(node.id)
        return frozenset(deps)

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
    def module(self) -> ast.Module:
        module = ast.parse(TEMPLATE)

        # inject function signature
        func = ast.parse('lambda:0').body[0].value
        func.args = self.func_args
        module.body[3].value = func

        # collect definitions for contract external deps
        deps = []
        for dep in self.dependencies:
            definition = self.context.get(dep)
            if not definition:
                continue
            deps.append(definition)

        # inject contract if contract is a function
        contract = copy(self.body)
        if isinstance(contract, ast.FunctionDef):
            contract.body = deps + contract.body
            # if contract is function, add it's definition and assign it's name
            # to `contract` variable.
            module.body = [contract] + module.body
            module.body[3].value = ast.Name(
                id=contract.name,
                lineno=1,
                col_offset=1,
                ctx=ast.Load(),
            )
            return module

        if isinstance(contract, ast.Expr):
            contract = contract.value

        # Inject contract if contract is a lambda.
        # We have to rebuild lambda into a function
        # to inject dependencies inside the body.
        if isinstance(contract, ast.Lambda):
            body = list(deps)
            return_node = ast.Return(
                value=contract.body,
                lineno=1,
                col_offset=1,
                ctx=ast.Load(),
            )
            body.append(return_node)
            var_name = module.body[2].targets[0].id
            func = ast.FunctionDef(
                name=var_name,
                args=contract.args,
                body=body,
                decorator_list=[],
                lineno=1,
                col_offset=1,
                ctx=ast.Load(),
            )
            module.body[2] = func
            return module

        # inject contract if contract is an unknown expression
        module.body[2].value = contract
        return module

    @cached_property
    def bytecode(self):
        return compile(self.module, filename='<ast>', mode='exec')

    def run(self, *args, **kwargs):
        globals = dict(args=args, kwargs=kwargs)
        exec(self.bytecode, globals)
        return globals['result']

    def __repr__(self) -> str:
        return '{name}({category})'.format(
            name=type(self).__name__,
            category=self.category.value,
        )
