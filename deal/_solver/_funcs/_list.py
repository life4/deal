from ._registry import register
from .._proxies import ListSort
from .._context import Context


@register('builtins.list.index')
def list_index(items: ListSort, item, start=None, **kwargs):
    return items.index(item, start=start)


@register('builtins.list.append')
def list_append(items: ListSort, item, ctx: Context, var_name: str, **kwargs) -> None:
    if not var_name.isidentifier():
        return
    ctx.scope.set(
        name=var_name,
        value=items.append(item),
    )


@register('builtins.list.extend')
def list_extend(items: ListSort, other, ctx: Context, var_name: str, **kwargs) -> None:
    if not var_name.isidentifier():
        return
    ctx.scope.set(
        name=var_name,
        value=items + other,
    )


@register('builtins.list.count')
def list_count(items: ListSort, item, **kwargs) -> None:
    return items.count(item)
