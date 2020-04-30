# built-in
from pathlib import Path

# external
import pytest

# project
from deal._cli._lint import get_errors, get_paths, lint_command


TEXT = """
import deal

@deal.post(lambda x: x > 0)
def f(x):
    return -1
"""


def test_get_paths(tmp_path: Path):
    (tmp_path / 'subdir').mkdir()
    (tmp_path / 'subdir' / '__pycache__').mkdir()
    (tmp_path / '.hidden').mkdir()

    (tmp_path / 'setup.py').touch()
    (tmp_path / 'subdir' / 'ex.py').touch()
    (tmp_path / '.hidden' / 'ex.py').touch()
    (tmp_path / 'subdir' / '__pycache__' / 'ex.py').touch()
    (tmp_path / 'setup.pl').touch()
    actual = {p.relative_to(tmp_path) for p in get_paths(tmp_path)}
    assert actual == {Path('setup.py'), Path('subdir/ex.py')}

    with pytest.raises(FileNotFoundError):
        list(get_paths(tmp_path / 'not_exists'))


def test_get_errors(tmp_path: Path):
    (tmp_path / 'example.py').write_text(TEXT)
    errors = list(get_errors(paths=[tmp_path]))
    assert len(errors) == 1
    assert errors[0]['code'] == 11
    assert errors[0]['content'] == '    return -1'


def test_lint_command(tmp_path: Path, capsys):
    (tmp_path / 'example.py').write_text(TEXT)
    count = lint_command([str(tmp_path)])
    assert count == 1

    captured = capsys.readouterr()
    assert 'return -1' in captured.out
    assert '(-1)' in captured.out
    assert '^' in captured.out


def test_lint_command_json(tmp_path: Path, capsys):
    (tmp_path / 'example.py').write_text(TEXT)
    count = lint_command(['--json', str(tmp_path)])
    assert count == 1

    captured = capsys.readouterr()
    assert '"    return -1"' in captured.out
    assert '"-1"' in captured.out
    assert '^' not in captured.out
