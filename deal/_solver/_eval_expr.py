import operator

import astroid
import z3

from ._context import Context
from ._registry import HandlersRegistry
from ._exceptions import UnsupportedError
from ._funcs import FUNCTIONS


eval_expr = HandlersRegistry()

CONSTS = {
    bool: z3.BoolVal,
    int: z3.IntVal,
    float: z3.RealVal,
    str: z3.StringVal,
}
COMAPARISON = {
    '<': operator.lt,
    '<=': operator.le,
    '>': operator.gt,
    '>=': operator.ge,
    '==': operator.eq,
    '!=': operator.ne,
}
UNARY_OPERATIONS = {
    '-': operator.neg,
    '+': operator.pos,
    '~': operator.inv,
    'not': z3.Not,
}
BIN_OPERATIONS = {
    # math
    '+': operator.add,
    '-': operator.sub,
    '*': operator.mul,
    # '/': operator.truediv,
    '//': operator.truediv,  # Z3 has Python2-like behavior
    '**': operator.pow,
    '%': operator.mod,
    '@': operator.matmul,

    # bitwise
    '&': operator.and_,
    '|': operator.or_,
    '^': operator.xor,
    '<<': operator.lshift,
    '>>': operator.rshift,
}
BOOL_OPERATIONS = {
    'and': z3.And,
    'or': z3.Or,
}


@eval_expr.register(astroid.Const)
def eval_const(node: astroid.Const, ctx: Context):
    t = type(node.value)
    converter = CONSTS.get(t)
    if not converter:
        raise UnsupportedError(repr(node.value))
    yield converter(node.value)


@eval_expr.register(astroid.BinOp)
def eval_bin_op(node: astroid.BinOp, ctx: Context):
    if not node.op:
        raise UnsupportedError('unsupported operator', node.op)
    operation = BIN_OPERATIONS.get(node.op)
    if not operation:
        raise UnsupportedError(repr(node.value))
    refs, left = eval_expr.split(node=node.left, ctx=ctx)
    yield from refs
    refs, right = eval_expr.split(node=node.right, ctx=ctx)
    yield from refs
    yield operation(left, right)


@eval_expr.register(astroid.Compare)
def eval_compare(node: astroid.Compare, ctx: Context):
    refs, left = eval_expr.split(node=node.left, ctx=ctx)
    yield from refs
    for op, right_node in node.ops:
        if not op:
            raise UnsupportedError(repr(node))
        operation = COMAPARISON.get(op)
        if not operation:
            raise UnsupportedError('unsupported operation', op, repr(node))

        refs, right = eval_expr.split(node=right_node, ctx=ctx)
        yield from refs
        yield operation(left, right)


@eval_expr.register(astroid.BoolOp)
def eval_bool_op(node: astroid.BoolOp, ctx: Context):
    if not node.op:
        raise UnsupportedError('unsupported operator', node.op)
    operation = BOOL_OPERATIONS.get(node.op)
    if not operation:
        raise UnsupportedError(repr(node.op))
    if not node.values:
        raise UnsupportedError('empty bool operator')

    subnodes = []
    for subnode in node.values:
        refs, right = eval_expr.split(node=subnode, ctx=ctx)
        yield from refs
        subnodes.append(right)
    yield operation(*subnodes)


@eval_expr.register(astroid.Name)
def eval_name(node: astroid.Name, ctx: Context):
    if not isinstance(node, astroid.Name):
        raise UnsupportedError(type(node))
    var = ctx.scope.get(node.name)
    if var is None:
        raise UnsupportedError('cannot resolve name', node.name)
    yield var


@eval_expr.register(astroid.UnaryOp)
def eval_unary_op(node: astroid.UnaryOp, ctx: Context):
    operation = UNARY_OPERATIONS.get(node.op)
    if operation is None:
        raise UnsupportedError('unary operation', node.op)
    refs, value_ref = eval_expr.split(node=node.operand, ctx=ctx)
    yield from refs
    yield operation(value_ref)


@eval_expr.register(astroid.IfExp)
def eval_ternary_op(node: astroid.IfExp, ctx: Context):
    if node.test is None:
        raise UnsupportedError(type(node))
    if node.body is None:
        raise UnsupportedError(type(node))
    if node.orelse is None:
        raise UnsupportedError(type(node))

    # execute child nodes
    refs, test_ref = eval_expr.split(node=node.test, ctx=ctx)
    yield from refs
    refs, then_ref = eval_expr.split(node=node.body, ctx=ctx)
    yield from refs
    refs, else_ref = eval_expr.split(node=node.orelse, ctx=ctx)
    yield from refs

    yield z3.If(test_ref, then_ref, else_ref)


@eval_expr.register(astroid.Call)
def eval_call(node: astroid.Call, ctx: Context):
    if not isinstance(node.func, astroid.Name):
        raise UnsupportedError('non-name call target', node.func)

    call_args = []
    for arg_node in node.args:
        refs, arg_node = eval_expr.split(node=arg_node, ctx=ctx)
        yield from refs
        call_args.append(arg_node)
    target = node.func.name

    # resolve built-in functions
    func = FUNCTIONS.get(target)
    if func is not None:
        yield func(*call_args)
        return

    raise UnsupportedError('unknown func', target)
