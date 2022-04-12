from __future__ import annotations

import ast

import astroid

from .common import TOKENS, Extractor, Token
from .value import UNKNOWN, get_value


get_asserts = Extractor()


@get_asserts.register(*TOKENS.ASSERT)
def handle_assert(expr: ast.Assert | astroid.Assert) -> Token | None:
    value = get_value(expr=expr.test, allow_inference=False)
    if value is UNKNOWN:
        return None
    if value:
        return None
    return Token(value=value, line=expr.lineno, col=expr.col_offset + 7)
