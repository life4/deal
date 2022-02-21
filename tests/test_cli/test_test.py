import sys
from io import StringIO
from pathlib import Path
from textwrap import dedent

import pytest

import deal
from deal._cli import main
from deal._cli._test import (
    fast_iterator, format_coverage, format_exception,
    has_pure_contract, run_cases, sys_path,
)
from deal._testing import TestCase
from deal._trace import TraceResult
from deal.linter._func import Func


def test_safe_violation(tmp_path: Path, capsys):
    if 'example' in sys.modules:
        del sys.modules['example']
    text = """
        import deal

        @deal.pure
        def func(a: int, b: int) -> float:
            return a / b
    """
    path = (tmp_path / 'example.py')
    path.write_text(dedent(text))
    stream = StringIO()
    result = main(['test', '--count', '1', str(path)], root=tmp_path, stream=stream)
    assert result == 1

    stream.seek(0)
    captured = stream.read()
    assert '/example.py' in captured
    assert 'running func' in captured
    assert 'func(a=0, b=0)' in captured
    assert 'ZeroDivisionError' in captured
    assert 'RaisesContractError' in captured


def test_no_violations(tmp_path: Path):
    if 'example' in sys.modules:
        del sys.modules['example']
    text = """
        import deal

        @deal.pure
        def func(a: int, b: int) -> float:
            return a + b

        def not_pure1(a: int, b: int) -> float:
            return a / b

        @deal.post(lambda result: result > 0)
        def not_pure2(a: int, b: int) -> float:
            return a / b
    """
    path = (tmp_path / 'example.py')
    path.write_text(dedent(text))
    stream = StringIO()
    result = main(['test', '--count', '5', str(path)], root=tmp_path, stream=stream)
    assert result == 0

    stream.seek(0)
    captured = stream.read()
    assert '/example.py' in captured
    assert 'running func' in captured
    assert 'not_pure' not in captured
    assert 'func(' not in captured


def test_no_matching_funcs(tmp_path: Path):
    if 'example' in sys.modules:
        del sys.modules['example']
    text = """
        import deal

        def not_pure1(a: int, b: int) -> float:
            return a / b

        @deal.post(lambda result: result > 0)
        def not_pure2(a: int, b: int) -> float:
            return a / b
    """
    path = (tmp_path / 'example.py')
    path.write_text(dedent(text))
    stream = StringIO()
    result = main(['test', '--count', '5', str(path)], root=tmp_path, stream=stream)
    assert result == 0

    stream.seek(0)
    captured = stream.read()
    assert '/example.py' not in captured


def test_sys_path():
    path = Path('example')
    size = len(sys.path)

    assert sys.path[0] != 'example'
    with sys_path(path):
        assert sys.path[0] == 'example'
    assert sys.path[0] != 'example'
    assert len(sys.path) == size

    with sys_path(path):
        del sys.path[0]
    assert len(sys.path) == size


@pytest.mark.parametrize('source, has', [
    ('@deal.pure \ndef f(): 0', True),
    ('@deal.pure() \ndef f(): 0', True),
    ('@deal.has() \ndef f(): 0', True),
    # ('@deal.has\ndef f(): 0', True),
])
def test_has_pure_contract(source: str, has: bool) -> None:
    funcs = Func.from_text(source)
    assert len(funcs) == 1
    assert has_pure_contract(funcs[0]) is has


def test_fast_iterator():
    seq = [1, 2, 3, 4]
    assert list(fast_iterator(iter(seq))) == seq


def test_print_exception():
    try:
        raise deal.PreContractError
    except deal.PreContractError:
        text = format_exception()
    assert text.startswith('    Traceback (most recent call last):\n')
    assert 'test_test.py' in text
    assert 'PreContractError' in text
    assert text.endswith('\x1b[39;49;00m')


@pytest.mark.parametrize('cov_l, all_l, exp', [
    ({2, 3, 4}, {2, 3, 4}, '    coverage <G>100%<E>'),
    ({2, 4}, {2, 3, 4}, '    coverage <Y>67%<E> (missing 3)'),
    ({2, 5}, {2, 3, 4, 5}, '    coverage <Y>50%<E> (missing 3-4)'),
    (set(), {2, 3, 4, 5}, '    coverage <R>0%<E>'),
])
def test_format_coverage_100(cov_l, all_l, exp):
    fake_colors = dict(
        red='<R>',
        yellow='<Y>',
        green='<G>',
        end='<E>',
    )
    tr = TraceResult('', 0, covered_lines=cov_l, all_lines=all_l)
    text = format_coverage(tr, colors=fake_colors)
    assert text == exp


def test_run_cases_ok():
    def func() -> int:
        return 123

    case = TestCase(
        args=(),
        kwargs={},
        func=func,
        exceptions=(),
        check_types=False,
    )
    colors = dict(
        blue='<B>',
        yellow='<Y>',
        end='<E>',
    )
    stream = StringIO()
    ok = run_cases(
        cases=iter([case]),
        func_name='fname',
        stream=stream,
        colors=colors,
    )
    assert ok
    stream.seek(0)
    captured = stream.read()
    assert captured
    assert captured.split('\n')[0] == '  <B>running fname<E>'


def test_run_cases_bad():
    def func(a, b):
        raise ZeroDivisionError

    case = TestCase(
        args=(1, ),
        kwargs=dict(b=2),
        func=func,
        exceptions=(),
        check_types=False,
    )
    colors = dict(
        blue='<B>',
        yellow='<Y>',
        end='<E>',
    )
    stream = StringIO()
    ok = run_cases(
        cases=iter([case]),
        func_name='fname',
        stream=stream,
        colors=colors,
    )
    assert not ok
    stream.seek(0)
    captured = stream.read()
    assert captured
    assert captured.split('\n')[0] == '  <B>running fname<E>'
    assert 'ZeroDivisionError' in captured
    assert 'Traceback' in captured
    assert '    <Y>fname(1, b=2)<E>' in captured
