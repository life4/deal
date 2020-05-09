# built-in
import ast
from contextlib import suppress

# external
import astroid

# app
from .common import Extractor, infer


inner_extractor = Extractor()
UNKNOWN = object()


def get_value(expr):
    if isinstance(expr, ast.AST):
        with suppress(ValueError, SyntaxError):
            return ast.literal_eval(expr)

    if isinstance(expr, astroid.node_classes.NodeNG):
        # AttributeError: 'AsStringVisitor3' object has no attribute 'visit_unknown'
        with suppress(AttributeError):  # pragma: no cover
            renderred = expr.as_string()
            with suppress(ValueError, SyntaxError):
                return ast.literal_eval(renderred)

    handler = inner_extractor.handlers.get(type(expr))
    if handler:
        value = handler(expr=expr)
        if value is not UNKNOWN:
            return value

    # astroid inference
    if hasattr(expr, 'infer'):
        for parent_expr in infer(expr=expr):
            if parent_expr == expr:  # avoid recursion
                continue
            value = get_value(expr=parent_expr)
            if value is not UNKNOWN:
                return value
    return UNKNOWN


@inner_extractor.register(astroid.List, astroid.Set, astroid.Tuple)
def handle_collections(expr):
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
