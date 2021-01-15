import z3
from .._proxies import wrap, StrSort, SetSort, unwrap, if_expr, ProxySort, random_name
from ._registry import register
from .._context import Context


@register('builtins.print')
def builtins_ignore(*args, **kwargs):
    return None


@register('builtins.sum')
def builtins_sum(items, ctx: Context, **kwargs):
    items = unwrap(items)
    f = z3.RecFunction(
        random_name('sum'),
        z3.IntSort(ctx=ctx.z3_ctx),
        items.sort().basis(),
    )
    i = z3.Int(random_name('index'), ctx=ctx.z3_ctx)
    one = z3.IntVal(1, ctx=ctx.z3_ctx)
    zero = z3.IntVal(0, ctx=ctx.z3_ctx)
    z3.RecAddDefinition(f, i, z3.If(
        i == zero,
        items[zero],
        items[i] + f(i - one),
    ))
    result = f(z3.Length(items) - one)
    return wrap(result)


# TODO: support more than 2 explicit arguments.
@register('builtins.min')
def builtins_min(a, b=None, *, ctx: Context, **kwargs):
    if b is not None:
        return wrap(z3.If(a < b, unwrap(a), unwrap(b)))

    items = unwrap(a)
    f = z3.RecFunction(
        random_name('min'),
        z3.IntSort(ctx=ctx.z3_ctx),
        items.sort().basis(),
    )
    i = z3.Int(random_name('index'))
    one = z3.IntVal(1, ctx=ctx.z3_ctx)
    zero = z3.IntVal(0, ctx=ctx.z3_ctx)
    z3.RecAddDefinition(f, i, z3.If(
        i == zero,
        items[zero],
        z3.If(
            items[i] < f(i - one),
            items[i],
            f(i - one),
            ctx=ctx.z3_ctx,
        ),
    ))
    result = f(z3.Length(items) - one)
    return wrap(result)


@register('builtins.max')
def builtins_max(a, b=None, *, ctx: Context, **kwargs):
    if b is not None:
        return wrap(z3.If(
            a > b,
            unwrap(a), unwrap(b),
            ctx=ctx.z3_ctx,
        ))

    items = unwrap(a)
    f = z3.RecFunction(
        random_name('max'),
        z3.IntSort(ctx=ctx.z3_ctx),
        items.sort().basis(),
    )
    i = z3.Int(random_name('index'), ctx=ctx.z3_ctx)
    one = z3.IntVal(1, ctx=ctx.z3_ctx)
    zero = z3.IntVal(0, ctx=ctx.z3_ctx)
    z3.RecAddDefinition(f, i, z3.If(
        i == zero,
        items[zero],
        z3.If(
            items[i] > f(i - one),
            items[i],
            f(i - one),
            ctx=ctx.z3_ctx,
        ),
        ctx=ctx.z3_ctx,
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
def builtins_int(a, *, ctx: Context, **kwargs):
    if isinstance(a, ProxySort):
        return a.as_int
    one = z3.IntVal(1, ctx=ctx.z3_ctx)
    zero = z3.IntVal(0, ctx=ctx.z3_ctx)
    return wrap(if_expr(a, one, zero, ctx=ctx.z3_ctx))


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
