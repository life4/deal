import operator
import typing

import astroid
import z3

from ._context import Context
from ._registry import HandlersRegistry
from ._exceptions import UnsupportedError
from ._funcs import FUNCTIONS
from ._sorts import ListSort, wrap, SetSort
from ..linter._extractors.common import get_full_name, infer


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
    'in': FUNCTIONS['syntax.in'],
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
    '/': FUNCTIONS['syntax./'],
    '//': FUNCTIONS['syntax.//'],
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
    return wrap(converter(node.value))


@eval_expr.register(astroid.BinOp)
def eval_bin_op(node: astroid.BinOp, ctx: Context):
    if not node.op:
        raise UnsupportedError('missed operator', node)
    operation = BIN_OPERATIONS.get(node.op)
    if not operation:
        raise UnsupportedError('unsupported operator', node.op)
    left = eval_expr(node=node.left, ctx=ctx)
    right = eval_expr(node=node.right, ctx=ctx)
    return operation(left, right)


@eval_expr.register(astroid.Compare)
def eval_compare(node: astroid.Compare, ctx: Context):
    left = eval_expr(node=node.left, ctx=ctx)
    for op, right_node in node.ops:
        if not op:
            raise UnsupportedError(repr(node))
        operation = COMAPARISON.get(op)
        if not operation:
            raise UnsupportedError('unsupported operation', op, repr(node))

        right = eval_expr(node=right_node, ctx=ctx)
        # TODO: proper chain
        return operation(left, right)


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
        right = eval_expr(node=subnode, ctx=ctx)
        subnodes.append(right)
    return operation(*subnodes)


@eval_expr.register(astroid.List)
def eval_list(node: astroid.List, ctx: Context):
    container = ListSort.make_empty()
    for subnode in node.elts:
        item = eval_expr(node=subnode, ctx=ctx)
        container = ListSort.append(container, item)
    return container


@eval_expr.register(astroid.Set)
def eval_set(node: astroid.Set, ctx: Context):
    container = SetSort.make_empty()
    for subnode in node.elts:
        item = eval_expr(node=subnode, ctx=ctx)
        container = SetSort.add(container, item)
    return container


@eval_expr.register(astroid.Name)
def eval_name(node: astroid.Name, ctx: Context):
    if not isinstance(node, astroid.Name):
        raise UnsupportedError(type(node))

    # resolve local vars
    value = ctx.scope.get(node.name)
    if value is not None:
        return value

    # resolve built-in functions
    value = FUNCTIONS.get('builtins.' + node.name)
    if value is not None:
        return value

    raise UnsupportedError('cannot resolve name', node.name)


@eval_expr.register(astroid.UnaryOp)
def eval_unary_op(node: astroid.UnaryOp, ctx: Context):
    operation = UNARY_OPERATIONS.get(node.op)
    if operation is None:
        raise UnsupportedError('unary operation', node.op)
    value_ref = eval_expr(node=node.operand, ctx=ctx)
    return operation(value_ref)


@eval_expr.register(astroid.IfExp)
def eval_ternary_op(node: astroid.IfExp, ctx: Context):
    if node.test is None:
        raise UnsupportedError(type(node))
    if node.body is None:
        raise UnsupportedError(type(node))
    if node.orelse is None:
        raise UnsupportedError(type(node))

    # execute child nodes
    test_ref = eval_expr(node=node.test, ctx=ctx)
    then_ref = eval_expr(node=node.body, ctx=ctx)
    else_ref = eval_expr(node=node.orelse, ctx=ctx)

    return z3.If(test_ref, then_ref, else_ref)


@eval_expr.register(astroid.Call)
def eval_call(node: astroid.Call, ctx: Context):
    call_args = []
    for arg_node in node.args:
        arg_node = eval_expr(node=arg_node, ctx=ctx)
        call_args.append(arg_node)
    if isinstance(node.func, astroid.Name):
        return _eval_call_name(node=node.func, ctx=ctx, call_args=call_args)

    if isinstance(node.func, astroid.Attribute):
        return _eval_call_attr(node=node.func, ctx=ctx, call_args=call_args)

    raise UnsupportedError('unsupported call target', node)


def _eval_call_name(node: astroid.Name, ctx: Context, call_args=typing.List[z3.Z3PPObject]):
    value = eval_expr(node=node, ctx=ctx)
    if not callable(value):
        raise UnsupportedError('the object is not callable ', node.name)
    return value(*call_args)


def _eval_call_attr(node: astroid.Attribute, ctx: Context, call_args=typing.List[z3.Z3PPObject]):
    # resolve methods
    definitions = infer(node)
    if len(definitions) != 1:
        raise UnsupportedError('cannot resolve', node)

    target = definitions[0]
    if isinstance(target, astroid.BoundMethod):
        obj_ref = eval_expr(node=node.expr, ctx=ctx)
        call_args = [obj_ref] + call_args

    target_name = '.'.join(get_full_name(target))
    func = FUNCTIONS.get(target_name)
    if func is not None:
        return func(*call_args)

    raise UnsupportedError('no definition for', target_name)


@eval_expr.register(astroid.Lambda)
def eval_lambda(node: astroid.Lambda, ctx: Context):
    def fake_func(*values):
        body_ctx = ctx.make_child()
        for arg, value in zip(node.args.arguments, values):
            body_ctx.scope.set(name=arg.name, value=value)
        return eval_expr(node=node.body, ctx=body_ctx)

    return fake_func
