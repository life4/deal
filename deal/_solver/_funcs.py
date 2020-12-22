import z3
from ._sorts import wrap, StrSort, SetSort, unwrap


FUNCTIONS = dict()


def register(name: str):
    def wrapper(func):
        FUNCTIONS[name] = func
        return func
    return wrapper


@register('builtins.min')
def builtin_min(a, b):
    return wrap(z3.If(a < b, unwrap(a), unwrap(b)))


@register('builtins.max')
def builtin_max(a, b):
    return wrap(z3.If(a > b, unwrap(a), unwrap(b)))


@register('builtins.abs')
def builtin_abs(a):
    return z3.If(a >= z3.IntVal(0), a, -a)


@register('builtins.len')
def builtin_len(items):
    return items.length()


@register('syntax./')
def syntax_truediv(left, right):
    if z3.is_int(left):
        left = z3.ToReal(left)
    if z3.is_int(right):
        right = z3.ToReal(right)
    return left / right


@register('syntax.//')
def syntax_floordiv(left, right):
    has_real = False
    if z3.is_real(left):
        has_real = True
        left = z3.ToInt(left)
    if z3.is_real(right):
        has_real = True
        right = z3.ToInt(right)
    result = left / right
    if has_real:
        result = z3.ToReal(result)
    return result


@register('syntax.in')
def syntax_in(item, items):
    return items.contains(item)


@register('builtins.int')
def builtin_int(a):
    if z3.is_string(a):
        return z3.StrToInt(a)
    return z3.ToInt(a)


@register('builtins.float')
def builtin_float(a):
    if z3.is_string(a):
        return z3.ToReal(z3.StrToInt(a))
    return z3.ToReal(a)


@register('builtins.str')
def builtin_str(obj) -> StrSort:
    return StrSort.convert(obj)


@register('builtins.set')
def builtin_set() -> StrSort:
    return SetSort.make_empty()


@register('builtins.str.startswith')
def str_startswith(seq, prefix):
    return seq.startswith(prefix)


@register('builtins.str.endswith')
def str_endswith(seq, suffix):
    return seq.endswith(suffix)


@register('builtins.str.index')
def str_index(items, item, start=None):
    return items.index(item, start=start)


@register('builtins.list.index')
def list_index(items, item, start=None):
    return items.index(item, start=start)


# @register('builtins.list.append')
# def list_append(a, b):
#     return z3.SuffixOf(b, a)
