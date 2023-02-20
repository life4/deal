from __future__ import annotations

import ast
import builtins
import enum
from copy import copy
from pathlib import Path
from types import CodeType
from typing import Iterable, Union

import astroid

from .._cached_property import cached_property


TEMPLATE = (Path(__file__).parent / '_template.py').read_text()
CONTRACT_INDEX = 3
FUNC_INDEX = 4


class Category(enum.Enum):
    ENSURE = 'ensure'
    EXAMPLE = 'example'
    HAS = 'has'
    POST = 'post'
    PRE = 'pre'
    PURE = 'pure'
    RAISES = 'raises'
    SAFE = 'safe'
    INHERIT = 'inherit'

    @property
    def brackets_optional(self) -> bool:
        return self in {Category.SAFE, Category.PURE}


class NoValidatorError(Exception):
    pass


class Contract:
    args: tuple[ast.expr | astroid.NodeNG, ...]
    kwargs: tuple[ast.keyword | astroid.Keyword, ...]
    category: Category
    func_args: ast.arguments
    context: dict[str, ast.stmt]
    line: int

    def __init__(
        self,
        args: Iterable[ast.expr | astroid.NodeNG],
        kwargs: Iterable[ast.keyword | astroid.Keyword],
        category: Category,
        func_args: ast.arguments,
        context: dict[str, ast.stmt] | None = None,
        line: int = 0,
    ) -> None:
        self.args = tuple(args)
        self.kwargs = tuple(kwargs)
        self.category = category
        self.func_args = func_args
        self.context = context or dict()
        self.line = line

    @cached_property
    def validator(self) -> ast.AST:
        """The validator converted into ast.
        """
        contract = self.raw_validator
        if isinstance(contract, ast.AST):
            return contract
        # convert astroid node to ast node
        contract = self._resolve_name(contract)
        return ast.parse(contract.as_string()).body[0]

    @cached_property
    def raw_validator(self) -> ast.expr | astroid.NodeNG:
        if self.args:
            return self.args[0]
        for kwarg in self.kwargs:
            if kwarg.arg == 'validator':
                return kwarg.value
        raise NoValidatorError('cannot find validator for contract')

    @cached_property
    def arguments(self) -> frozenset[str]:
        """Contract function arguments names.

        Useful for resolving external dependencies.
        """
        func = self.validator
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
        return frozenset(result)

    @cached_property
    def dependencies(self) -> frozenset[str]:
        """Names that are defined outside of the contract body.

        1. Excludes built-in objects.
        1. Excludes contract function arguments.
        """
        deps = set()
        for node in ast.walk(self.validator):
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
    def exceptions(self) -> list[Union[str, type[BaseException]]]:
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
        func = ast.Lambda(
            args=self.func_args,
            body=ast.Set(elts=[], ctx=ast.Load()),
            ctx=ast.Load(),
        )
        module.body[FUNC_INDEX].value = func  # type: ignore

        # collect definitions for contract external deps
        deps: list[ast.stmt] = []
        for dep in self.dependencies:
            definition = self.context.get(dep)
            if not definition:
                continue
            deps.append(definition)

        # inject contract if contract is a function
        contract = copy(self.validator)
        if isinstance(contract, ast.FunctionDef):
            contract.body = deps + contract.body
            # if contract is function, add it's definition and assign it's name
            # to `contract` variable.
            module.body = [contract] + module.body
            module.body[FUNC_INDEX].value = ast.Name(  # type: ignore[attr-defined]
                id=contract.name,
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
                ctx=ast.Load(),
            )
            body.append(return_node)
            module.body[CONTRACT_INDEX] = ast.FunctionDef(
                name='contract',
                args=contract.args,
                body=body,
                decorator_list=[],
                ctx=ast.Load(),
            )
            return module

        # inject contract if contract is an unknown expression
        module.body[CONTRACT_INDEX].value = contract  # type: ignore[attr-defined]
        return module

    @cached_property
    def bytecode(self) -> CodeType:
        module = ast.fix_missing_locations(self.module)
        return compile(module, filename='<ast>', mode='exec')

    def run(self, *args, **kwargs):
        globals = dict(args=args, kwargs=kwargs)
        exec(self.bytecode, globals)
        return globals['result']

    def __repr__(self) -> str:
        return f'{type(self).__name__}({self.category.value})'
