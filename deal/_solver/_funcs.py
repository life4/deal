import z3
from ._context import Context
from ._proxies import wrap, StrSort, SetSort, FloatSort, IntSort, unwrap, if_expr
from ._exceptions import UnsupportedError


FUNCTIONS = dict()


def register(name: str):
    def wrapper(func):
        FUNCTIONS[name] = func
        return func
    return wrapper


@register('builtins.min')
def builtin_min(a, b=None, **kwargs):
    if b is None:
        raise UnsupportedError('min from iterable is unsupported')
    return wrap(z3.If(a < b, unwrap(a), unwrap(b)))


@register('builtins.max')
def builtin_max(a, b=None, **kwargs):
    if b is None:
        raise UnsupportedError('max from iterable is unsupported')
    return wrap(z3.If(a > b, unwrap(a), unwrap(b)))


@register('builtins.abs')
def builtin_abs(a, **kwargs):
    return a.abs


@register('builtins.len')
def builtin_len(items, **kwargs):
    return items.length()


@register('syntax.in')
def syntax_in(item, items, **kwargs):
    return items.contains(item)


@register('builtins.int')
def builtin_int(a, **kwargs):
    return a.as_int


@register('builtins.float')
def builtin_float(a, **kwargs):
    return a.as_float


@register('builtins.str')
def builtin_str(obj, **kwargs) -> StrSort:
    return obj.as_str


@register('builtins.set')
def builtin_set(**kwargs) -> StrSort:
    return SetSort.make_empty()


@register('builtins.str.startswith')
def str_startswith(seq, prefix, **kwargs):
    return seq.startswith(prefix)


@register('builtins.str.endswith')
def str_endswith(seq, suffix, **kwargs):
    return seq.endswith(suffix)


@register('builtins.str.index')
def str_index(items, item, start=None, **kwargs):
    return items.index(item, start=start)


@register('builtins.list.index')
def list_index(items, item, start=None, **kwargs):
    return items.index(item, start=start)


@register('builtins.list.append')
def list_append(items, item, ctx: Context, var_name: str, **kwargs) -> None:
    if not var_name.isidentifier():
        return
    ctx.scope.set(
        name=var_name,
        value=items.append(item),
    )


@register('builtins.list.extend')
def list_extend(items, other, ctx: Context, var_name: str, **kwargs) -> None:
    if not var_name.isidentifier():
        return
    ctx.scope.set(
        name=var_name,
        value=items + other,
    )


@register('math.isclose')
def math_isclose(left, right, rel_tol=None, abs_tol=None, **kwargs) -> None:
    if isinstance(left, IntSort) and isinstance(right, IntSort):
        return left == right

    if isinstance(left, IntSort):
        left = left.as_float
    if isinstance(right, IntSort):
        right = right.as_float
    assert isinstance(left, FloatSort)
    assert isinstance(right, FloatSort)

    if rel_tol is None:
        rel_tol = wrap(FloatSort.val(1e-09))
    if abs_tol is None:
        abs_tol = wrap(FloatSort.val(0.0))

    delta = builtin_max(rel_tol * builtin_max(left.abs, right.abs), abs_tol)
    return if_expr(
        z3.And(left.is_nan, right.is_nan),
        z3.BoolVal(True),
        (left - right).abs <= delta,
    )
