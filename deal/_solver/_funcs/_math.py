import z3
from .._proxies import FloatSort, IntSort, if_expr
from ._registry import register, FUNCTIONS


@register('math.isclose')
def math_isclose(left, right, rel_tol=None, abs_tol=None, **kwargs) -> None:
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
