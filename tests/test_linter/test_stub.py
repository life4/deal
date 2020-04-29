import json
from pathlib import Path

import pytest

from deal.linter._contract import Category
from deal.linter._stub import generate_stub, StubFile


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


def test_do_not_dump_empty_stub(tmp_path: Path):
    root = tmp_path / 'project'
    root.mkdir()
    (root / '__init__.py').touch()
    source_path = (root / 'example.py')
    source_path.write_text("def func(): return 1")
    stub_path = generate_stub(path=source_path)
    assert not stub_path.exists()
    assert stub_path.name == 'example.json'
    assert stub_path.parent == root


def test_stub_file(tmp_path: Path):
    path = tmp_path / 'example.json'
    stub = StubFile(path=path)

    # add
    stub.add(func='fname', contract=Category.RAISES, value='TypeError')
    with pytest.raises(ValueError, match='unsupported contract'):
        stub.add(func='fname', contract=Category.POST, value='SyntaxError')
    assert stub._content == {'fname': {'raises': ['TypeError']}}

    # get
    assert stub.get(func='fname', contract=Category.RAISES) == frozenset({'TypeError'})
    with pytest.raises(ValueError, match='unsupported contract'):
        stub.get(func='fname', contract=Category.POST)
    assert stub.get(func='unknown', contract=Category.RAISES) == frozenset()

    # dump
    stub.dump()
    content = json.loads(path.read_text(encoding='utf8'))
    assert content == {'fname': {'raises': ['TypeError']}}

    # load
    stub2 = StubFile(path=path)
    stub2.load()
    assert stub2._content == {'fname': {'raises': ['TypeError']}}
