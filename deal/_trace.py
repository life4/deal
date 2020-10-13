from typing import Any, NamedTuple, Set
from trace import Trace
import inspect

from ._testing import TestCase


class TraceResult(NamedTuple):
    file_name: str
    func_name: str
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
    func_name = func.__name__
    file_name = func.__code__.co_filename
    lines, first_line = inspect.getsourcelines(func)
    last_line = first_line + len(lines)

    covered_lines: Set[int] = set()
    for (fname, lineno), _hits in t.counts.items():
        if fname != file_name:
            continue
        if lineno < first_line:
            continue
        if lineno > last_line:
            continue
        covered_lines.add(lineno)

    body_start_line = last_line
    if len(covered_lines) > 1:
        body_start_line = sorted(covered_lines)[1]

    return TraceResult(
        func_name=func_name,
        file_name=file_name,
        func_result=func_result,
        covered_lines=covered_lines,
        total_lines=last_line - body_start_line + 1,
    )
