from pathlib import Path

import pytest

from deal.linter._cli import get_errors, get_paths


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
    errors = list(get_errors([tmp_path]))
    assert len(errors) == 1
    assert errors[0]['code'] == 11
    assert errors[0]['content'] == '    return -1'
