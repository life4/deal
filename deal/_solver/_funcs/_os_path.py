# external
import z3

# app
from .._proxies import wrap
from ._registry import register


@register('os.path.join')
def os_path_join(first_arg, *args, **kwargs):
    sep = wrap(z3.StringVal("/"))
    for arg in args:
        first_arg = first_arg + sep + arg
    return first_arg
