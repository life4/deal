import json
from pathlib import Path
# from textwrap import dedent
from deal.linter._stub import generate_stub


def test_generate_stub(tmp_path: Path):
    root = tmp_path / 'project'
    root.mkdir()
    (root / '__init__.py').touch()
    source_path = (root / 'example.py')
    source_path.write_text("def func(): 1/0")
    stub_path = generate_stub(path=source_path)
    content = json.loads(stub_path.read_text())
    assert stub_path.name == 'example.json'
    assert stub_path.parent == root
    assert content == {'func': {'raises': ['ZeroDivisionError']}}
