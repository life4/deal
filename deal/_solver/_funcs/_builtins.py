import z3
from .._proxies import wrap, StrSort, SetSort, unwrap
from .._exceptions import UnsupportedError
from ._registry import register


@register('builtins.min')
def builtisn_min(a, b=None, **kwargs):
    if b is None:
        raise UnsupportedError('min from iterable is unsupported')
    return wrap(z3.If(a < b, unwrap(a), unwrap(b)))


@register('builtins.max')
def builtisn_max(a, b=None, **kwargs):
    if b is None:
        raise UnsupportedError('max from iterable is unsupported')
    return wrap(z3.If(a > b, unwrap(a), unwrap(b)))


@register('builtins.abs')
def builtisn_abs(a, **kwargs):
    return a.abs


@register('builtins.len')
def builtisn_len(items, **kwargs):
    return items.length()


@register('builtins.int')
def builtisn_int(a, **kwargs):
    return a.as_int


@register('builtins.float')
def builtin_sfloat(a, **kwargs):
    return a.as_float


@register('builtins.str')
def builtisn_str(obj, **kwargs) -> StrSort:
    return obj.as_str


@register('builtins.bool')
def builtins_bool(obj, **kwargs) -> z3.BoolRef:
    return obj.as_bool


@register('builtins.set')
def builtisn_set(**kwargs) -> StrSort:
    return SetSort.make_empty()
