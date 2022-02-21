import ast
from contextlib import suppress
from typing import Union

import astroid

from .common import infer


UNKNOWN = object()
Node = Union[ast.AST, astroid.NodeNG]


def get_value(expr: Node, allow_inference: bool = True) -> object:
    if isinstance(expr, ast.AST):
        with suppress(ValueError, SyntaxError):
            return ast.literal_eval(expr)

    if isinstance(expr, astroid.NodeNG):
        # AttributeError: 'AsStringVisitor3' object has no attribute 'visit_unknown'
        with suppress(AttributeError):  # pragma: no cover
            renderred = expr.as_string()
            with suppress(ValueError, SyntaxError):
                return ast.literal_eval(renderred)

    value = _parse_collections(expr=expr)
    if value is not UNKNOWN:
        return value

    if allow_inference:
        for parent_expr in infer(expr=expr):
            if parent_expr == expr:  # avoid recursion
                continue
            value = get_value(expr=parent_expr)
            if value is not UNKNOWN:
                return value
    return UNKNOWN


def _parse_collections(expr: Node) -> object:
    if not isinstance(expr, (astroid.List, astroid.Set, astroid.Tuple)):
        return UNKNOWN

    result = []
    for element_expr in expr.elts:
        value = get_value(expr=element_expr)
        if value is UNKNOWN:
            return UNKNOWN
        result.append(value)

    if type(expr) is astroid.Tuple:
        return tuple(result)
    if type(expr) is astroid.Set:
        return set(result)
    return result
