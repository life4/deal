# built-in
import sys
from io import StringIO
from pathlib import Path
from textwrap import dedent

# external
import pytest

# project
from deal._cli._test import (
    has_pure_contract, sys_path, test_command as command,
    fast_iterator
)
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
    result = command(['--count', '1', str(path)], root=tmp_path, stream=stream)
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
    result = command(['--count', '5', str(path)], root=tmp_path, stream=stream)
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
    result = command(['--count', '5', str(path)], root=tmp_path, stream=stream)
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
