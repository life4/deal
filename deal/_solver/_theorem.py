import enum
import typing
from textwrap import dedent

import astroid
import z3

from ._context import Context
from ._exceptions import UnsupportedError, ProveError
from ._eval_expr import eval_expr
from ._eval_stmt import eval_stmt
from .._cached_property import cached_property
from ..linter._extractors.contracts import get_contracts


class Conclusion(enum.Enum):
    OK = 'proved!'
    SKIP = 'skipped'
    FAIL = 'failed'


SORTS = {
    'bool': z3.BoolSort,
    'int': z3.IntSort,
    'float': z3.RealSort,
    'str': z3.StringSort,
}
z3.Z3_DEBUG = False


class Theorem:
    _func: astroid.FunctionDef
    conclusion: typing.Optional[Conclusion] = None
    error: typing.Optional[Exception] = None
    example: typing.Optional[z3.ModelRef] = None

    def __init__(self, node: astroid.FunctionDef) -> None:
        self._func = node

    @classmethod
    def from_text(cls, content: str) -> typing.Iterator['Theorem']:
        content = dedent(content)
        module = astroid.parse(content)
        yield from cls.from_astroid(module)

    @classmethod
    def from_astroid(cls, module: astroid.Module) -> typing.Iterator['Theorem']:
        for node in module.values():
            if isinstance(node, astroid.FunctionDef):
                yield cls(node=node)

    @property
    def name(self) -> str:
        return self._func.name or 'unknown_function'

    @cached_property
    def context(self) -> Context:
        ctx = Context.make_empty()
        for name, value in self.arguments.items():
            ctx.scope.set(name=name, value=value)
        return ctx

    @cached_property
    def contracts(self) -> typing.Dict[str, z3.Goal]:
        goals = dict(
            pre=z3.Goal(),
            post=z3.Goal(),
        )
        if not self._func.decorators:
            return goals
        return_value = self.context.scope.get('return')
        for contract_name, args in get_contracts(self._func.decorators.nodes):
            if contract_name not in {'pre', 'post'}:
                continue
            if contract_name == 'post' and return_value is None:
                continue
            contract = args[0]
            if not isinstance(contract, astroid.Lambda):
                continue
            if not contract.args:
                continue

            cargs = contract.args.arguments
            if contract_name == 'post':
                self.context.scope.set(
                    name=cargs[0].name,
                    value=return_value,
                )
            for value in eval_expr(node=contract.body, ctx=self.context):
                goals[contract_name].add(value)
        return goals

    @cached_property
    def arguments(self) -> typing.Dict[str, z3.SortRef]:
        result = dict()
        args: astroid.Arguments = self._func.args
        for arg, annotation in zip(args.args, args.annotations):
            sort = self._annotation_to_sort(annotation)
            if sort is None:
                raise UnsupportedError('unsupported annotation type', annotation)
            result[arg.name] = z3.Const(name=arg.name, sort=sort())
        return result

    @staticmethod
    def _annotation_to_sort(node: astroid.node_classes.NodeNG):
        if isinstance(node, astroid.Name):
            return SORTS.get(node.name)
        if isinstance(node, astroid.Const) and type(node.value) is str:
            return SORTS.get(node.value)
        return None

    @cached_property
    def constraint(self) -> z3.BoolRef:
        asserts = z3.Goal(ctx=self.context.z3_ctx)
        for constraint in eval_stmt(node=self._func, ctx=self.context):
            asserts.add(constraint)
        asserts.add(self.contracts['post'].as_expr())

        return z3.And(
            # pre-condition must be always true
            self.contracts['pre'].as_expr(),
            # try to break body asserts or post-condition
            z3.Not(asserts.as_expr()),
        )

    @cached_property
    def solver(self) -> z3.Solver:
        solver = z3.Solver(ctx=self.context.z3_ctx)
        solver.add(self.constraint)
        return solver

    def reset(self) -> None:
        func = self._func
        self.__dict__.clear()
        self._func = func

    def prove(self) -> None:
        if self.conclusion is not None:
            raise RuntimeError('already proved')
        try:
            result = self.solver.check()
        except UnsupportedError as exc:
            self.conclusion = Conclusion.SKIP
            self.error = exc
            return

        if result == z3.unsat:
            self.conclusion = Conclusion.OK
            return

        if result == z3.unknown:
            self.conclusion = Conclusion.SKIP
            self.error = ProveError('cannot validate theorem')
            return

        if result == z3.sat:
            self.conclusion = Conclusion.FAIL
            self.example = self.solver.model()
            return

        raise RuntimeError('unreachable')
