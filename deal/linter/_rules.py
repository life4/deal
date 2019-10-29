import enum
from typing import Iterator

from ._error import Error
from ._extractors import get_exceptions, get_returns
from ._func import Func, Category


rules = []


class Required(enum.Enum):
    FUNC = 'func'
    AST = 'ast'


def register(rule):
    rules.append(rule())
    return rule


@register
class CheckReturns:
    code = 1
    message = 'post contract error'
    required = Required.FUNC

    def __call__(self, func: Func) -> Iterator[Error]:
        if func.category != Category.POST:
            return
        for token in get_returns(body=func.body):
            result = func.run(token.value)
            error_info = dict(row=token.line, col=token.col, code=self.code)
            if isinstance(result, str):
                yield Error(text=result, **error_info)
                continue
            if not result:
                yield Error(text=self.message, **error_info)


@register
class CheckRaises:
    code = 2
    message = 'raises contract error ({exc})'
    required = Required.FUNC

    def __call__(self, func: Func) -> Iterator[Error]:
        if func.category != Category.RAISES:
            return
        allowed = func.exceptions.copy()
        if not allowed:
            return
        for token in get_exceptions(body=func.body):
            if token.value in allowed:
                continue
            exc = token.value
            if not isinstance(exc, str):
                exc = exc.__name__
            yield Error(
                code=self.code,
                text=self.message.format(exc=exc),
                row=token.line,
                col=token.col,
            )
