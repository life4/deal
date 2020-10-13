from typing import Any, NamedTuple, Optional, Set, Tuple
from trace import Trace
import ast
import inspect

from ._testing import TestCase


class TraceResult(NamedTuple):
    file_name: str
    func_result: Any
    covered_lines: Set[int]
    total_lines: int

    @property
    def coverage(self) -> float:
        if not self.total_lines:
            return 0
        return self.covered_lines / self.total_lines


def trace(case: TestCase) -> TraceResult:
    t = Trace(trace=False)
    func_result = t.runfunc(case)

    func = inspect.unwrap(case.func)
    file_name = func.__code__.co_filename
    first_line, last_line = _get_func_body_range(func=func)

    covered_lines: Set[int] = set()
    for (fname, lineno), _hits in t.counts.items():
        if fname != file_name:
            continue
        if lineno < first_line:
            continue
        if lineno > last_line:
            continue
        covered_lines.add(lineno)

    return TraceResult(
        file_name=file_name,
        func_result=func_result,
        covered_lines=covered_lines,
        total_lines=last_line - first_line + 1,
    )


def _get_func_body_range(func) -> Tuple[int, int]:
    func_name = func.__name__
    file_name = func.__code__.co_filename

    with open(file_name) as stream:
        tree = ast.parse(stream.read(), filename=file_name)

    node = _get_func_node(func_name=func_name, tree=tree)
    if node is None:
        first_line = func.__code__.co_firstlineno
        return (first_line, first_line + 1)

    return (node.body[0].lineno + 1, node.body[-1].lineno)


def _get_func_node(func_name: str, tree: ast.Module) -> Optional[ast.FunctionDef]:
    for node in tree.body:
        if not isinstance(node, ast.FunctionDef):
            continue
        if node.name != func_name:
            continue
        return node
    return None
