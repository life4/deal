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

    refs, value_ref = eval_expr.split(node=node.value, ctx=ctx)
    yield from refs

    # var = z3.Const(name=target_name, sort=value.sort())
    ctx.scope.set(name=target_name, value=value_ref)
    # yield var == value


@eval_stmt.register(astroid.Return)
def eval_return(node: astroid.Return, ctx: Context):
    refs, value_ref = eval_expr.split(node=node.value, ctx=ctx)
    yield refs
    ctx.scope.set(name='return', value=value_ref)
