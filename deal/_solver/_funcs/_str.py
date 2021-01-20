# app
from ._registry import register


@register('builtins.str.startswith')
def str_startswith(seq, prefix, **kwargs):
    return seq.startswith(prefix)


@register('builtins.str.endswith')
def str_endswith(seq, suffix, **kwargs):
    return seq.endswith(suffix)


@register('builtins.str.index')
def str_index(items, item, start=None, **kwargs):
    return items.index(item, start=start)
