import ast
from pathlib import Path

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
        (6, 4, 'DEAL011: post contract error', Checker),
        (11, 4, 'DEAL012: raises contract error (ZeroDivisionError)', Checker),
        (13, 4, 'DEAL012: raises contract error (KeyError)', Checker),
    ]
    assert errors == expected


def test_astroid_path(tmp_path: Path):
    path = tmp_path / 'test.py'
    path.write_text(TEXT)
    checker = Checker(tree=ast.parse(TEXT), filename=str(path))
    errors = list(checker.run())
    expected = [
        (6, 4, 'DEAL011: post contract error', Checker),
        (11, 4, 'DEAL012: raises contract error (ZeroDivisionError)', Checker),
        (13, 4, 'DEAL012: raises contract error (KeyError)', Checker),
    ]
    assert errors == expected
