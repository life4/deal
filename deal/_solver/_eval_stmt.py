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


@eval_stmt.register(astroid.Assign)
def eval_assign(node: astroid.Assign, ctx: Context):
    if not node.targets:
        raise UnsupportedError('assignment to an empty target')
    if len(node.targets) > 1:
        raise UnsupportedError('multiple assignment')
    target = node.targets[0]
    if not isinstance(target, astroid.AssignName):
        raise UnsupportedError('assignment target', type(target))
    target_name = target.name

    values = list(eval_expr(node=node.value, ctx=ctx))
    yield from values[:-1]
    value = values[-1]

    # var = z3.Const(name=target_name, sort=value.sort())
    ctx.scope.set(name=target_name, var=value)
    # yield var == value
