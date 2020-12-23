import z3
from ._registry import registry


def unwrap(obj) -> z3.Z3PPObject:
    from ._proxy import ProxySort

    if not isinstance(obj, ProxySort):
        return obj
    expr = obj.expr
    if expr is None:
        return obj.make_empty_expr(z3.IntSort())
    return expr


def wrap(expr):
    from ._proxy import ProxySort

    if isinstance(expr, ProxySort):
        return expr
    if z3.is_string(expr):
        return registry['str'](expr=expr)
    if z3.is_seq(expr):
        return registry['list'](expr=expr)
    if z3.is_array(expr):
        return registry['set'](expr=expr)
    if z3.is_fp(expr):
        return registry['float'](expr=expr)
    if z3.is_real(expr):
        return registry['float'](expr=expr)
    if z3.is_int(expr):
        return registry['int'](expr=expr)
    return expr


def if_expr(test, val_then, val_else):
    return wrap(z3.If(test, unwrap(val_then), unwrap(val_else)))
