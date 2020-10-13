from typing import Any, Iterator, NamedTuple, Optional, Set, Tuple
from trace import Trace
import ast
import inspect

from ._testing import TestCase


class TraceResult(NamedTuple):
    file_name: str
    func_result: Any
    covered_lines: Set[int]
    first_line: int
    last_line: int

    @property
    def total_lines(self) -> int:
        return self.last_line - self.first_line + 1

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
        first_line=first_line,
        last_line=last_line,
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


def format_lines(statements: Set[int], lines: Set[int]) -> str:
    return ', '.join(_nice_pair(*pair) for pair in _line_ranges(statements, lines))


def _nice_pair(start: int, end: int) -> str:
    if start == end:
        return str(start)
    return '{}-{}'.format(start, end)


def _line_ranges(statements: Set[int], lines: Set[int]) -> Iterator[Tuple[int, int]]:
    statements = sorted(statements)
    lines = sorted(lines)
    start = 0
    end = 0
    lidx = 0
    for stmt in statements:
        if lidx >= len(lines):
            break
        if stmt == lines[lidx]:
            lidx += 1
            if not start:
                start = stmt
            end = stmt
        elif start:
            yield (start, end)
            start = None
    if start:
        yield (start, end)
