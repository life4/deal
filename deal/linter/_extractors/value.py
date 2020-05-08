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


@inner_extractor.register(astroid.Const)
def handle_const(expr: astroid.Const):
    return expr.value
