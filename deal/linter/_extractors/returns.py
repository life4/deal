# built-in
from typing import Optional

# app
from .common import TOKENS, Extractor, Token, traverse
from .value import get_value, UNKNOWN


get_returns = Extractor()
inner_extractor = Extractor()


def has_returns(body: list) -> bool:
    for expr in traverse(body=body):
        if isinstance(expr, TOKENS.RETURN + TOKENS.YIELD):
            return True
    return False


@get_returns.register(*TOKENS.RETURN)
def handle_return(expr) -> Optional[Token]:
    value = get_value(expr=expr.value)
    if value is UNKNOWN:
        return None
    return Token(value=value, line=expr.lineno, col=expr.value.col_offset)
