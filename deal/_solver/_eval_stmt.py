import astroid
import z3

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


@eval_stmt.register(astroid.If)
def eval_if_else(node: astroid.If, ctx: Context):
    if node.test is None:
        raise UnsupportedError(type(node))
    if node.body is None:
        raise UnsupportedError(type(node))

    refs, test_ref = eval_expr.split(node=node.test, ctx=ctx)
    yield refs

    ctx_then = ctx.make_child()
    for subnode in node.body:
        yield from eval_stmt(node=subnode, ctx=ctx_then)
    ctx_else = ctx.make_child()
    for subnode in (node.orelse or []):
        yield from eval_stmt(node=subnode, ctx=ctx_else)

    changed_vars = set(ctx_then.scope.layer) | set(ctx_else.scope.layer)
    for var_name in changed_vars:
        val_then = ctx_then.scope.get(name=var_name)
        val_else = ctx_else.scope.get(name=var_name)
        if val_then is None or val_else is None:
            raise UnsupportedError('unbound variable', var_name)

        value = z3.If(test_ref, val_then, val_else)
        ctx.scope.set(name=var_name, value=value)
