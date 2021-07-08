from io import StringIO
from pathlib import Path
from textwrap import dedent

from deal._cli import main


def test_incorrect(tmp_path: Path):
    text = """
        import deal

        @deal.post(lambda x: x > 0)
        def func(x: int):
            return -1
    """
    path = (tmp_path / 'example.py')
    path.write_text(dedent(text))
    stream = StringIO()
    result = main(['prove', str(path), '--nocolor'], stream=stream)

    stream.seek(0)
    captured = stream.read()
    assert result == 1, captured
    assert '/example.py\n' in captured
    assert ' func\n' in captured
    assert ' failed post-condition' in captured


def test_correct(tmp_path: Path):
    text = """
        import deal

        @deal.post(lambda x: x > 0)
        def func(x: int):
            return 1
    """
    path = (tmp_path / 'example.py')
    path.write_text(dedent(text))
    stream = StringIO()
    result = main(['prove', str(path), '--nocolor'], stream=stream)

    stream.seek(0)
    captured = stream.read()
    assert result == 0, captured
    assert '/example.py\n' in captured
    assert ' func\n' in captured
    assert ' proved! post-condition' in captured


def test_skip(tmp_path: Path):
    text = """
        import deal

        def func(x):
            assert x > 0
    """
    path = (tmp_path / 'example.py')
    path.write_text(dedent(text))
    result = main(['prove', str(path), '--nocolor'])
    assert result == 0


def test_skip_show_skipped(tmp_path: Path):
    text = """
        import deal

        def func(x):
            assert x > 0
    """
    path = (tmp_path / 'example.py')
    path.write_text(dedent(text))
    stream = StringIO()
    result = main(['prove', str(path), '--nocolor', '--skipped'], stream=stream)

    stream.seek(0)
    captured = stream.read()
    assert result == 0, captured
    assert '/example.py\n' in captured
    assert ' func\n' in captured
    exp = 'skipped failed to interpret function arguments (missed annotation for x)\n'
    assert exp in captured


def test_skip_tests(tmp_path: Path):
    text = """
        import deal

        def test_func():
            assert False
    """
    path = (tmp_path / 'example.py')
    path.write_text(dedent(text))
    result = main(['prove', str(path), '--nocolor'])
    assert result == 0


def test_prove_no_decorators_fail(tmp_path: Path):
    text = """
        import deal

        def func():
            assert False
    """
    path = (tmp_path / 'example.py')
    path.write_text(dedent(text))
    result = main(['prove', str(path), '--nocolor'])
    assert result == 1


def test_prove_no_decorators_ok(tmp_path: Path):
    text = """
        import deal

        def func():
            assert True
    """
    path = (tmp_path / 'example.py')
    path.write_text(dedent(text))
    result = main(['prove', str(path), '--nocolor'])
    assert result == 0


def test_show_filename_once(tmp_path: Path):
    text = """
        import deal

        def func1():
            assert True
        def func2():
            assert True
    """
    path = (tmp_path / 'example.py')
    path.write_text(dedent(text))
    stream = StringIO()
    result = main(['prove', str(path), '--nocolor'], stream=stream)
    stream.seek(0)
    captured = stream.read()
    assert result == 0, captured
    assert 'func1' in captured
    assert 'func2' in captured
    assert captured.count('example.py') == 1
