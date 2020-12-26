import math
import z3
from .._proxies import FloatSort, IntSort, if_expr, wrap
from ._registry import register, FUNCTIONS


@register('math.isclose')
def math_isclose(left, right, rel_tol=None, abs_tol=None, **kwargs):
    if not isinstance(left, FloatSort) and not isinstance(right, FloatSort):
        return left == right

    if isinstance(left, IntSort):
        left = left.as_float
    if isinstance(right, IntSort):
        right = right.as_float

    if rel_tol is None:
        rel_tol = FloatSort.val(1e-09)
    if abs_tol is None:
        abs_tol = FloatSort.val(0.0)

    if FloatSort.prefer_real:
        left = left.as_real
        right = right.as_real
    else:
        left = left.as_fp
        right = right.as_fp

    builtin_max = FUNCTIONS['builtins.max']
    delta = builtin_max(rel_tol * builtin_max(left.abs, right.abs), abs_tol)
    return if_expr(
        z3.And(left.is_nan, right.is_nan),
        z3.BoolVal(True),
        (left - right).abs <= delta,
    )


@register('math.isinf')
def math_isinf(x, **kwargs):
    if not isinstance(x, FloatSort):
        return z3.BoolVal(False)
    if not x.is_fp:
        return z3.BoolVal(False)
    return z3.fpIsInf(x.expr)


@register('math.isnan')
def math_isnan(x, **kwargs):
    if not isinstance(x, FloatSort):
        return z3.BoolVal(False)
    if not x.is_fp:
        return z3.BoolVal(False)
    return z3.fpIsNaN(x.expr)


@register('math.sin')
def math_sin(x, **kwargs):
    """Taylor's Series of sin x
    """
    if not isinstance(x, FloatSort):
        x = x.as_float

    series = [
        (False, 3),
        (True, 5),
        (False, 7),
        (True, 9),
        (False, 11),
    ]
    result = x
    nominator = x
    for positive, pow in series:
        nominator = nominator * x * x
        denominator = wrap(z3.IntVal(math.factorial(pow)))
        if positive:
            result += nominator / denominator
        else:
            result -= nominator / denominator
    return result
