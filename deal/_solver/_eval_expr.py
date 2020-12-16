import operator

import astroid
import z3

from ._context import Context
from ._registry import HandlersRegistry
from ._exceptions import UnsupportedError


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
BIN_OPERATIONS = {
    # math
    '+': operator.add,
    '-': operator.sub,
    '*': operator.mul,
    '/': operator.truediv,
    '**': operator.pow,
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
    lefts = list(eval_expr(node=node.left, ctx=ctx))
    yield from lefts[:-1]
    rights = list(eval_expr(node=node.right, ctx=ctx))
    yield from rights[:-1]
    yield operation(lefts[-1], rights[-1])


@eval_expr.register(astroid.Compare)
def eval_compare(node: astroid.Compare, ctx: Context):
    lefts = list(eval_expr(node=node.left, ctx=ctx))
    yield from lefts[:-1]
    for op, right_node in node.ops:
        if not op:
            raise UnsupportedError(repr(node))
        operation = COMAPARISON.get(op)
        if not operation:
            raise UnsupportedError('unsupported operation', op, repr(node))

        rights = list(eval_expr(node=right_node, ctx=ctx))
        yield from rights[:-1]
        yield operation(lefts[-1], rights[-1])


@eval_expr.register(astroid.Assign)
def eval_assign(node: astroid.Assign, ctx: Context):
    if not node.targets:
        raise UnsupportedError('assignment to an empty target')
    if len(node.targets) > 1:
        raise UnsupportedError('multiple assignment')
    # target = node.targets[0]
    ...
    raise UnsupportedError()
