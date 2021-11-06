import ast
import inspect
import sys
from trace import Trace
from typing import Any, Callable, Iterator, NamedTuple, Optional, Set, Tuple


class TraceResult(NamedTuple):
    file_name: str
    func_result: Any
    covered_lines: Set[int]
    all_lines: Set[int]

    @property
    def coverage(self) -> int:
        return round(len(self.covered_lines) * 100 / len(self.all_lines))


class Only(NamedTuple):
    file_name: str

    def names(self, filename: str, modulename: str) -> int:
        return int(filename != self.file_name)


def trace(func: Callable, **kwargs) -> TraceResult:
    # find the file where the original function is defined
    original_func = inspect.unwrap(func)
    file_name = original_func.__code__.co_filename

    t = Trace(trace=False)
    # Ignore everything except the file where the function is defined.
    # It makes the tracing much faster.
    t.ignore = Only(file_name)  # type: ignore

    old_trace = sys.gettrace()
    try:
        func_result: Any = t.runfunc(func, **kwargs)
    finally:
        # restore previous tracer
        sys.settrace(old_trace)     # pragma: no cover
    return _collect_trace_results(  # pragma: no cover
        t=t,
        func=original_func,
        file_name=file_name,
        func_result=func_result,
    )


# this is a separate function to restore coverage for it after playing with trace hooks.
def _collect_trace_results(t: Trace, func, file_name: str, func_result) -> TraceResult:
    all_lines = _get_func_body_statements(func=func)
    first_line = min(all_lines)
    last_line = max(all_lines)

    covered_lines: Set[int] = set()
    for fname, lineno in t.counts:  # type: ignore
        assert fname == file_name
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
    )


def _get_func_body_statements(func: Callable) -> Set[int]:
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
            pairs.append(f'{start}-{end}')
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
