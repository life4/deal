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
def builtin_len(a):
    return z3.Length(a)


@register('syntax.in')
def builtin_in(a, b):
    return z3.Contains(b, a)


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
