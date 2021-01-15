import z3
from .._proxies import wrap, StrSort, SetSort, unwrap, if_expr, ProxySort
from ._registry import register


@register('builtins.sum')
def builtins_sum(items, **kwargs):
    items = unwrap(items)
    f = z3.RecFunction('min', z3.IntSort(), items.sort().basis())
    i = z3.Int('i')
    one = z3.IntVal(1)
    zero = z3.IntVal(0)
    z3.RecAddDefinition(f, i, z3.If(
        i == zero,
        items[zero],
        items[i] + f(i - one),
    ))
    result = f(z3.Length(items) - one)
    return wrap(result)


# TODO: support more than 2 explicit arguments.
@register('builtins.min')
def builtins_min(a, b=None, **kwargs):
    if b is not None:
        return wrap(z3.If(a < b, unwrap(a), unwrap(b)))

    items = unwrap(a)
    f = z3.RecFunction('min', z3.IntSort(), items.sort().basis())
    i = z3.Int('i')
    one = z3.IntVal(1)
    zero = z3.IntVal(0)
    z3.RecAddDefinition(f, i, z3.If(
        i == zero,
        items[zero],
        z3.If(
            items[i] < f(i - one),
            items[i],
            f(i - one),
        ),
    ))
    result = f(z3.Length(items) - one)
    return wrap(result)


@register('builtins.max')
def builtins_max(a, b=None, **kwargs):
    if b is not None:
        return wrap(z3.If(a > b, unwrap(a), unwrap(b)))

    items = unwrap(a)
    f = z3.RecFunction('min', z3.IntSort(), items.sort().basis())
    i = z3.Int('i')
    one = z3.IntVal(1)
    zero = z3.IntVal(0)
    z3.RecAddDefinition(f, i, z3.If(
        i == zero,
        items[zero],
        z3.If(
            items[i] > f(i - one),
            items[i],
            f(i - one),
        ),
    ))
    result = f(z3.Length(items) - one)
    return wrap(result)


@register('builtins.abs')
def builtins_abs(a, **kwargs):
    return a.abs


@register('builtins.len')
def builtins_len(items, **kwargs):
    return items.length


@register('builtins.int')
def builtins_int(a, **kwargs):
    if isinstance(a, ProxySort):
        return a.as_int
    return wrap(if_expr(a, z3.IntVal(1), z3.IntVal(0)))


@register('builtins.float')
def builtins_float(a, **kwargs):
    return a.as_float


@register('builtins.str')
def builtins_str(obj, **kwargs) -> StrSort:
    return obj.as_str


@register('builtins.bool')
def builtins_bool(obj, **kwargs) -> z3.BoolRef:
    if isinstance(obj, ProxySort):
        return obj.as_bool
    return obj


@register('builtins.set')
def builtins_set(**kwargs) -> SetSort:
    return SetSort.make_empty()
