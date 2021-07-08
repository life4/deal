import ast
from typing import Dict, Union

import astroid


TreeType = Union[ast.Module, astroid.Module]
DefsType = Dict[str, ast.stmt]


def get_definitions(tree: TreeType) -> DefsType:
    if isinstance(tree, ast.Module):
        return _extract_defs_ast(tree)
    return _extract_defs_astroid(tree)


def _extract_defs_ast(tree: ast.Module) -> DefsType:
    result: DefsType = dict()
    for node in tree.body:
        if isinstance(node, ast.Import):
            for name_node in node.names:
                name = name_node.asname or name_node.name
                result[name] = ast.Import(
                    names=[name_node],
                    lineno=1,
                    col_offset=1,
                    ctx=ast.Load(),
                )
            continue

        if isinstance(node, ast.ImportFrom):
            if not node.module or node.level:
                continue
            for name_node in node.names:
                name = name_node.asname or name_node.name
                result[name] = ast.ImportFrom(
                    module=node.module,
                    names=[name_node],
                    lineno=1,
                    col_offset=1,
                    ctx=ast.Load(),
                )
            continue

        if isinstance(node, ast.Assign):
            for target in node.targets:
                if not isinstance(target, ast.Name):
                    continue
                result[target.id] = node
    return result


def _extract_defs_astroid(tree: astroid.Module) -> DefsType:
    result: DefsType = dict()
    for node in tree.body:
        if isinstance(node, astroid.Import):
            for name, alias in node.names:
                result[alias or name] = ast.Import(
                    names=[ast.alias(name=name, asname=alias)],
                    lineno=1,
                    col_offset=1,
                    ctx=ast.Load(),
                )
            continue

        if isinstance(node, astroid.ImportFrom):
            if not node.modname or node.level:
                continue
            for name, alias in node.names:
                result[alias or name] = ast.ImportFrom(
                    module=node.modname,
                    names=[ast.alias(name=name, asname=alias)],
                    lineno=1,
                    col_offset=1,
                    ctx=ast.Load(),
                )
            continue

        if isinstance(node, astroid.Assign):
            expr = ast.parse(node.as_string()).body[0]
            for target in node.targets:
                if not isinstance(target, astroid.AssignName):
                    continue
                result[target.name] = expr
    return result
