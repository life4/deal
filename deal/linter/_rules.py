import enum
from typing import Iterator

from ._error import Error
from ._extractors import get_exceptions, get_returns, get_imports, get_prints
from ._func import Func, Category


rules = []


class Required(enum.Enum):
    FUNC = 'func'
    MODULE = 'module'


def register(rule):
    rules.append(rule())
    return rule


@register
class CheckImports:
    code = 1
    message = 'do not use `from deal import ...`, use `import deal` instead'
    required = Required.MODULE

    def __call__(self, tree) -> Iterator[Error]:
        for token in get_imports(tree.body):
            if token.value == 'deal':
                yield Error(
                    code=self.code,
                    text=self.message,
                    row=token.line,
                    col=token.col,
                )


@register
class CheckReturns:
    code = 11
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
    code = 12
    message = 'raises contract error ({exc})'
    required = Required.FUNC

    def __call__(self, func: Func) -> Iterator[Error]:
        if func.category != Category.RAISES:
            return
        allowed = func.exceptions.copy()
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


@register
class CheckPrints:
    code = 13
    message = 'silent contract error ({func})'
    required = Required.FUNC

    def __call__(self, func: Func) -> Iterator[Error]:
        if func.category != Category.SILENT:
            return
        for token in get_prints(body=func.body):
            yield Error(
                code=self.code,
                text=self.message.format(func=token.value),
                row=token.line,
                col=token.col,
            )
