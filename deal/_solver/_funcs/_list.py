import typing
from ._registry import register

if typing.TYPE_CHECKING:
    from .._context import Context


@register('builtins.list.index')
def list_index(items, item, start=None, **kwargs):
    return items.index(item, start=start)


@register('builtins.list.append')
def list_append(items, item, ctx: 'Context', var_name: str, **kwargs) -> None:
    if not var_name.isidentifier():
        return
    ctx.scope.set(
        name=var_name,
        value=items.append(item),
    )


@register('builtins.list.extend')
def list_extend(items, other, ctx: 'Context', var_name: str, **kwargs) -> None:
    if not var_name.isidentifier():
        return
    ctx.scope.set(
        name=var_name,
        value=items + other,
    )
