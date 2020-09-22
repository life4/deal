import ast
import astroid
from typing import Dict, Union


TreeType = Union[ast.Module, astroid.Module]


def get_definitions(tree: TreeType) -> Dict[str, ast.AST]:
    if isinstance(tree, ast.Module):
        return _extract_defs_ast(tree)
    return _extract_defs_astroid(tree)


def _extract_defs_ast(tree: ast.Module) -> Dict[str, ast.AST]:
    result: Dict[str, ast.AST] = dict()
    for node in tree.body:
        if isinstance(node, ast.Import):
            for name_node in node.names:
                stmt = ast.Import(
                    names=[name_node],
                    lineno=1,
                    col_offset=1,
                    ctx=ast.Load(),
                )
                name = name_node.asname or name_node.name
                result[name] = stmt
            continue

        if isinstance(node, ast.ImportFrom):
            module_name = '.' * node.level + node.module
            for name_node in node.names:
                stmt = ast.ImportFrom(
                    module=module_name,
                    names=[name_node],
                    lineno=1,
                    col_offset=1,
                    ctx=ast.Load(),
                )
                name = name_node.asname or name_node.name
                result[name] = stmt
            continue

        if isinstance(node, ast.Expr):
            node = node.value
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if not isinstance(target, ast.Name):
                    continue
                result[target.id] = node
    return result


def _extract_defs_astroid(tree: astroid.Module) -> Dict[str, ast.AST]:
    result: Dict[str, ast.AST] = dict()
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
            module_name = '.' * (node.level or 0) + node.modname
            for name, alias in node.names:
                result[alias or name] = ast.ImportFrom(
                    module=module_name,
                    names=[ast.alias(name=name, asname=alias)],
                    lineno=1,
                    col_offset=1,
                    ctx=ast.Load(),
                )
            continue

        if isinstance(node, astroid.Expr):
            node = node.value
        if isinstance(node, astroid.Assign):
            expr = ast.parse(node.as_string()).body[0]
            for target in node.targets:
                if not isinstance(target, astroid.AssignName):
                    continue
                result[target.name] = expr
    return result
