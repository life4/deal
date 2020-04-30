# built-in
import json
from pathlib import Path

# project
from deal._cli._stub import stub_command


TEXT = """
import deal

def f(x):
    raise PatheticError
"""


def test_stub_command(tmp_path: Path):
    path = (tmp_path / 'example.py')
    path.write_text(TEXT)
    result = stub_command(['--iterations', '1', str(path)])
    assert result == 0
    content = (tmp_path / 'example.json').read_text()
    assert json.loads(content) == {'f': {'raises': ['PatheticError']}}
