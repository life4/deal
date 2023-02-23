import json
from pathlib import Path

import pytest

from deal._cli import main


try:
    import astroid
except ImportError:
    astroid = None


TEXT = """
import deal

def f(x):
    raise PatheticError
"""


@pytest.mark.skipif(astroid is None, reason='astroid is not installed')
def test_stub_command(tmp_path: Path):
    path = (tmp_path / 'example.py')
    path.write_text(TEXT)
    result = main(['stub', '--iterations', '1', str(path)])
    assert result == 0
    content = (tmp_path / 'example.json').read_text()
    assert json.loads(content) == {'f': {'raises': ['PatheticError']}}
