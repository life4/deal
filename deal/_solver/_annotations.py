import astroid
import z3
from ..linter._extractors.common import get_full_name, get_name, infer

SIMPLE_SORTS = {
    'bool': z3.BoolSort,
    'int': z3.IntSort,
    'float': z3.RealSort,
    'str': z3.StringSort,
}
GENERIC_SORTS = {
    'list': z3.SeqSort,
}


def ann2sort(node: astroid.node_classes.NodeNG):
    print(type(node))
    if isinstance(node, astroid.Name):
        return _sort_from_name(node=node)
    if isinstance(node, astroid.Const) and type(node.value) is str:
        return _sort_from_str(node=node)
    if isinstance(node, astroid.Subscript):
        return _sort_from_getattr(node=node)
    return None


def _sort_from_name(node: astroid.Name):
    sort = SIMPLE_SORTS.get(node.name)
    if sort is None:
        return None
    return sort()


def _sort_from_str(node: astroid.Const):
    sort = SIMPLE_SORTS.get(node.value)
    if sort is None:
        return None
    return sort()


def _sort_from_getattr(node: astroid.Subscript):
    definitions = infer(node)
    if len(definitions) != 1:
        return None

    _, type_name = get_full_name(definitions[0])
    if type_name != '_SpecialGenericAlias':
        return

    type_name = get_name(node.value).lower()
    sort = GENERIC_SORTS.get(type_name)
    if sort is None:
        return None

    subsort = ann2sort(node=node.slice)
    if subsort is None:
        return None
    print(5, type(subsort))
    return sort(subsort)
