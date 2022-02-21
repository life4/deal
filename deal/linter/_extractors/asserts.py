import ast
from typing import Optional, Union

import astroid

from .common import TOKENS, Extractor, Token
from .value import UNKNOWN, get_value


get_asserts = Extractor()


@get_asserts.register(*TOKENS.ASSERT)
def handle_assert(expr: Union[ast.Assert, astroid.Assert]) -> Optional[Token]:
    value = get_value(expr=expr.test, allow_inference=False)
    if value is UNKNOWN:
        return None
    if value:
        return None
    return Token(value=value, line=expr.lineno, col=expr.col_offset + 7)
