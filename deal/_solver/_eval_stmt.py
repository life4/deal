import astroid

from ._context import Context
from ._registry import HandlersRegistry
from ._eval_expr import eval_expr
from ._exceptions import UnsupportedError


eval_stmt = HandlersRegistry()


@eval_stmt.register(astroid.FunctionDef)
def eval_func(node: astroid.FunctionDef, ctx: Context):
    for statement in node.body:
        yield from eval_stmt(node=statement, ctx=ctx)


@eval_stmt.register(astroid.Assert)
def eval_assert(node: astroid.Assert, ctx: Context):
    if node.test is None:
        raise UnsupportedError('assert without condition')
    yield from eval_expr(node=node.test, ctx=ctx)
