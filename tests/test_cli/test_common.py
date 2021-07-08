from pathlib import Path

import pytest

from deal._cli._common import get_paths


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
