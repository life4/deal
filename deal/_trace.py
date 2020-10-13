from typing import Any, Iterator, NamedTuple, Optional, Set, Tuple
from trace import Trace
import ast
import inspect

from ._testing import TestCase


class TraceResult(NamedTuple):
    file_name: str
    func_result: Any
    covered_lines: Set[int]
    all_lines: Set[int]
    first_line: int
    last_line: int

    @property
    def total_lines(self) -> int:
        return self.last_line - self.first_line + 1


def trace(case: TestCase) -> TraceResult:
    t = Trace(trace=False)
    func_result: Any = t.runfunc(case)  # type: ignore

    func = inspect.unwrap(case.func)
    file_name = func.__code__.co_filename
    all_lines = _get_func_body_statements(func=func)
    first_line = min(all_lines)
    last_line = max(all_lines)

    covered_lines: Set[int] = set()
    for (fname, lineno), _hits in t.counts.items():  # type: ignore
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
        all_lines=all_lines,
        first_line=first_line,
        last_line=last_line,
    )


def _get_func_body_statements(func) -> Set[int]:
    func_name = func.__name__
    file_name = func.__code__.co_filename

    with open(file_name) as stream:
        tree = ast.parse(stream.read(), filename=file_name)

    func_node = _get_func_node(func_name=func_name, tree=tree)
    if func_node is None:
        first_line = func.__code__.co_firstlineno
        return {first_line}

    result: Set[int] = set()
    for statement in func_node.body:
        for node in ast.walk(statement):
            # skip nodes without lineno
            if not isinstance(node, ast.stmt):
                continue
            # skip docstring
            if isinstance(node, ast.Expr) and isinstance(node.value, ast.Str):
                continue
            result.add(node.lineno)
    return result


def _get_func_node(func_name: str, tree: ast.Module) -> Optional[ast.FunctionDef]:
    for node in tree.body:
        if not isinstance(node, ast.FunctionDef):
            continue
        if node.name != func_name:
            continue
        return node
    return None


def format_lines(statements: Set[int], lines: Set[int]) -> str:
    pairs = []
    for start, end in _line_ranges(statements, lines):
        if start == end:
            pairs.append(str(start))
        else:
            pairs.append('{}-{}'.format(start, end))
    return ', '.join(pairs)


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
            start = 0
    if start:
        yield (start, end)
