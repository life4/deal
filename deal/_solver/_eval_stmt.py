import astroid
import z3

from ._context import Context
from ._registry import HandlersRegistry
from ._eval_expr import eval_expr
from ._exceptions import UnsupportedError
from ._annotations import ann2sort
from ._proxies import if_expr, unwrap, ProxySort


eval_stmt = HandlersRegistry()


@eval_stmt.register(astroid.FunctionDef)
def eval_func(node: astroid.FunctionDef, ctx: Context):
    # if it is a recursive call, fake the function
    if node.name in ctx.trace:
        args = [unwrap(v) for v in ctx.scope.layer.values()]
        # generate function signature
        sorts = [arg.sort() for arg in args]
        if not node.returns:
            raise UnsupportedError('no return type annotation for', node.name)
        sorts.append(ann2sort(node.returns))

        func = z3.Function(node.name, *sorts)
        ctx.scope.set(
            name='return',
            value=func(*args),
        )
        return

    # otherwise, try to execute it
    with ctx.trace.guard(node.name):
        for statement in node.body:
            eval_stmt(node=statement, ctx=ctx)


@eval_stmt.register(astroid.Assert)
def eval_assert(node: astroid.Assert, ctx: Context):
    if node.test is None:
        raise UnsupportedError('assert without condition')
    expr = eval_expr(node=node.test, ctx=ctx)
    if isinstance(expr, ProxySort):
        expr = expr.as_bool
    ctx.expected.add(expr)


@eval_stmt.register(astroid.Expr)
def eval_expr_stmt(node: astroid.Expr, ctx: Context):
    eval_expr(node=node.value, ctx=ctx)


@eval_stmt.register(astroid.Assign)
def eval_assign(node: astroid.Assign, ctx: Context):
    if not node.targets:
        raise UnsupportedError('assignment to an empty target')
    if len(node.targets) > 1:
        raise UnsupportedError('multiple assignment')
    target = node.targets[0]
    if not isinstance(target, astroid.AssignName):
        raise UnsupportedError('assignment target', type(target))

    value_ref = eval_expr(node=node.value, ctx=ctx)
    ctx.scope.set(name=target.name, value=value_ref)


@eval_stmt.register(astroid.Return)
def eval_return(node: astroid.Return, ctx: Context):
    value_ref = eval_expr(node=node.value, ctx=ctx)
    ctx.scope.set(name='return', value=value_ref)


@eval_stmt.register(astroid.If)
def eval_if_else(node: astroid.If, ctx: Context):
    if node.test is None:
        raise UnsupportedError(type(node))
    if node.body is None:
        raise UnsupportedError(type(node))

    test_ref = eval_expr(node=node.test, ctx=ctx)

    ctx_then = ctx.make_child()
    for subnode in node.body:
        eval_stmt(node=subnode, ctx=ctx_then)
    ctx_else = ctx.make_child()
    for subnode in (node.orelse or []):
        eval_stmt(node=subnode, ctx=ctx_else)

    changed_vars = set(ctx_then.scope.layer) | set(ctx_else.scope.layer)
    for var_name in changed_vars:
        val_then = ctx_then.scope.get(name=var_name)
        val_else = ctx_else.scope.get(name=var_name)
        if val_then is None or val_else is None:
            raise UnsupportedError('unbound variable', var_name)

        value = if_expr(test_ref, val_then, val_else)
        ctx.scope.set(name=var_name, value=value)


@eval_stmt.register(astroid.Global)
@eval_stmt.register(astroid.ImportFrom)
@eval_stmt.register(astroid.Import)
@eval_stmt.register(astroid.Pass)
def eval_skip(node, ctx: Context):
    pass
