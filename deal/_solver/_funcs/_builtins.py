import z3
from .._proxies import wrap, StrSort, SetSort, unwrap
from .._exceptions import UnsupportedError
from ._registry import register


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
