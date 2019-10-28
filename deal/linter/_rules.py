from ._error import Error
from ._extractors import get_returns
from ._func import Func, Category


rules = []


def register(rule):
    rules.append(rule)
    return rule


@register
def check_returns(func: Func):
    if func.category != Category.POST:
        return
    for token in get_returns(body=func.body):
        result = func.run(token.value)
        error_info = dict(row=token.line, col=token.col, code=1)
        if isinstance(result, str):
            yield Error(text=result, **error_info)
            continue
        if not result:
            yield Error(text='post contract error', **error_info)
