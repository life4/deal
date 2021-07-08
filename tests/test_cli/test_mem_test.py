import sys
from io import StringIO
from pathlib import Path
from textwrap import dedent

from deal._cli import main


def test_has_side_effect(tmp_path: Path, capsys):
    if 'example' in sys.modules:
        del sys.modules['example']
    text = """
        import deal

        a = []

        @deal.pure
        def func(b: int) -> float:
            a.append({b, b+b})
            return None
    """
    path = (tmp_path / 'example.py')
    path.write_text(dedent(text))
    stream = StringIO()
    result = main(['memtest', '--count', '1', str(path)], root=tmp_path, stream=stream)
    assert result == 1

    stream.seek(0)
    captured = stream.read()
    assert '/example.py' in captured
    assert 'running func' in captured
    assert 'func(b=0)' in captured
    assert 'set' in captured
    assert 'x1' in captured


def test_no_side_effects(tmp_path: Path, capsys):
    if 'example' in sys.modules:
        del sys.modules['example']
    text = """
        import deal

        @deal.pure
        def func(b: int) -> float:
            return b+b
    """
    path = (tmp_path / 'example.py')
    path.write_text(dedent(text))
    stream = StringIO()
    result = main(['memtest', '--count', '1', str(path)], root=tmp_path, stream=stream)
    assert result == 0

    stream.seek(0)
    captured = stream.read()
    assert '/example.py' in captured
    assert 'running func' in captured
    assert 'func(b=0)' not in captured


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
    result = main(['memtest', str(path)], root=tmp_path, stream=stream)
    assert result == 0

    stream.seek(0)
    captured = stream.read()
    assert '/example.py' not in captured
