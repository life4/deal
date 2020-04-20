# built-in
import ast
from pathlib import Path

# project
from deal.linter import Checker


TEXT = """
import deal


@deal.post(lambda x: x > 0)
def test():
    return -1


@deal.raises(ValueError)
def test2():
    1 / 0
    raise ValueError
    raise KeyError
""".strip()


def test_stdin():
    checker = Checker(tree=ast.parse(TEXT))
    errors = list(checker.run())
    expected = [
        (6, 11, 'DEAL011: post contract error (-1)', Checker),
        (11, 8, 'DEAL012: raises contract error (ZeroDivisionError)', Checker),
        (13, 10, 'DEAL012: raises contract error (KeyError)', Checker),
    ]
    assert errors == expected


def test_astroid_path(tmp_path: Path):
    path = tmp_path / 'test.py'
    path.write_text(TEXT)
    checker = Checker(tree=ast.parse(TEXT), filename=str(path))
    errors = list(checker.run())
    expected = [
        (6, 11, 'DEAL011: post contract error (-1)', Checker),
        (11, 8, 'DEAL012: raises contract error (ZeroDivisionError)', Checker),
        (13, 10, 'DEAL012: raises contract error (KeyError)', Checker),
    ]
    assert errors == expected


def test_version():
    version = Checker(tree=None, filename='stdin').version
    assert not set(version) - set('0123456789.')
