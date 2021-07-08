from io import StringIO
from pathlib import Path

from deal._cli import main
from deal._cli._lint import LintCommand


TEXT = """
import deal

@deal.post(lambda x: x > 0)
def f(x):
    return -1
"""


def test_get_errors(tmp_path: Path):
    (tmp_path / 'example.py').write_text(TEXT)
    errors = list(LintCommand.get_errors(paths=[str(tmp_path)]))
    assert len(errors) == 1
    assert errors[0]['code'] == 'DEAL012'
    assert errors[0]['content'] == '    return -1'


def test_lint_command_colors(tmp_path: Path):
    (tmp_path / 'example.py').write_text(TEXT)
    stream = StringIO()
    count = main(['lint', str(tmp_path)], stream=stream)
    assert count == 1

    stream.seek(0)
    captured = stream.read()
    assert '\x1b[34mreturn\x1b[39;49;00m -\x1b[34m1\x1b[39;49;00m' in captured
    assert '\x1b[95m(-1)\x1b[0m' in captured
    assert '\x1b[95m^\x1b[0m' in captured


def test_lint_command_no_color(tmp_path: Path):
    (tmp_path / 'example.py').write_text(TEXT)
    stream = StringIO()
    count = main(['lint', '--nocolor', str(tmp_path)], stream=stream)
    assert count == 1

    stream.seek(0)
    captured = stream.read()
    exp = '6:11 DEAL012 post contract error (-1) return -1 ^'
    assert captured.split()[1:] == exp.split()


def test_lint_command_two_files(tmp_path: Path):
    (tmp_path / 'example1.py').write_text(TEXT)
    (tmp_path / 'example2.py').write_text(TEXT)
    stream = StringIO()
    count = main(['lint', '--nocolor', str(tmp_path)], stream=stream)
    assert count == 2

    stream.seek(0)
    captured = stream.read()
    assert 'example1.py' in captured
    assert 'example2.py' in captured
    assert 'return -1' in captured
    assert '(-1)' in captured
    assert '^' in captured


def test_lint_command_two_errors(tmp_path: Path):
    (tmp_path / 'example.py').write_text('from deal import pre\n' + TEXT)
    stream = StringIO()
    count = main(['lint', '--nocolor', str(tmp_path)], stream=stream)
    assert count == 2

    stream.seek(0)
    captured = stream.read()
    assert 'return -1' in captured
    assert '(-1)' in captured
    assert '^' in captured


def test_lint_command_json(tmp_path: Path):
    (tmp_path / 'example.py').write_text(TEXT)
    stream = StringIO()
    count = main(['lint', '--json', str(tmp_path)], stream=stream)
    assert count == 1

    stream.seek(0)
    captured = stream.read()
    assert '"    return -1"' in captured
    assert '"-1"' in captured
    assert '^' not in captured
