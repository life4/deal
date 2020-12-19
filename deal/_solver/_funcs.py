import z3
from ._exceptions import UnsupportedError


FUNCTIONS = dict()


def register(name: str):
    def wrapper(func):
        FUNCTIONS[name] = func
        return func
    return wrapper


@register('builtins.min')
def builtin_min(a, b):
    return z3.If(a < b, a, b)


@register('builtins.max')
def builtin_max(a, b):
    return z3.If(a > b, a, b)


@register('builtins.abs')
def builtin_abs(a):
    return z3.If(a >= z3.IntVal(0), a, -a)


@register('builtins.len')
def builtin_len(items):
    if isinstance(items, z3.ArrayRef):
        raise UnsupportedError('set length is unsupported')
    return z3.Length(items)


@register('syntax./')
def builtin_div(left, right):
    if z3.is_int(left):
        left = z3.ToReal(left)
    if z3.is_int(right):
        right = z3.ToReal(right)
    return left / right


@register('syntax.in')
def builtin_in(item, items):
    # str
    if z3.is_string(items):
        return z3.Contains(items, item)

    # set
    if isinstance(items, z3.ArrayRef):
        return z3.IsMember(e=item, s=items)

    # list
    return z3.Contains(items, z3.Unit(item))


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
def builtin_str(a):
    if z3.is_int(a):
        return z3.IntToStr(a)
    raise UnsupportedError('convert to str', type(a))


@register('builtins.str.startswith')
def str_startswith(a, b):
    return z3.PrefixOf(b, a)


@register('builtins.str.endswith')
def str_endswith(a, b):
    return z3.SuffixOf(b, a)


# @register('builtins.list.append')
# def list_append(a, b):
#     return z3.SuffixOf(b, a)
