# built-in
import typing

# external
import astroid
import z3

# app
from ..linter._extractors.common import get_full_name, get_name, infer
from ._proxies import FloatSort
from ._types import AstNode, SortType


SIMPLE_SORTS = {
    'bool': z3.BoolSort,
    'int': z3.IntSort,
    'float': FloatSort.sort,
    'str': z3.StringSort,
}
GENERIC_SORTS = {
    'list': z3.SeqSort,
    'set': z3.SetSort,
}
MaybeSort = typing.Optional[SortType]


def ann2sort(node: AstNode, ctx: z3.Context) -> MaybeSort:
    if isinstance(node, astroid.Index):
        return ann2sort(node=node.value, ctx=ctx)
    if isinstance(node, astroid.Name):
        return _sort_from_name(node=node, ctx=ctx)
    if isinstance(node, astroid.Const) and type(node.value) is str:
        return _sort_from_str(node=node, ctx=ctx)
    if isinstance(node, astroid.Subscript):
        return _sort_from_getattr(node=node, ctx=ctx)
    return None


def _sort_from_name(node: astroid.Name, ctx: z3.Context) -> MaybeSort:
    sort = SIMPLE_SORTS.get(node.name)
    if sort is None:
        return None
    return sort(ctx=ctx)


def _sort_from_str(node: astroid.Const, ctx: z3.Context) -> MaybeSort:
    sort = SIMPLE_SORTS.get(node.value)
    if sort is None:
        return None
    return sort(ctx=ctx)


def _sort_from_getattr(node: astroid.Subscript, ctx: z3.Context) -> MaybeSort:
    definitions = infer(node.value)
    if len(definitions) != 1:
        return None

    module_name, _ = get_full_name(definitions[0])
    if module_name != 'typing' and module_name != 'builtins':
        return None

    type_name = (get_name(node.value) or '').lower()
    sort = GENERIC_SORTS.get(type_name)
    if sort is None:
        return None

    subsort = ann2sort(node=node.slice, ctx=ctx)
    if subsort is None:
        return None
    return sort(subsort)
