import ast
from pathlib import Path
from textwrap import dedent

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

EXPECTED = [
    (6, 11, 'DEAL012 post contract error (-1)', Checker),
    (11, 8, 'DEAL021 raises contract error (ZeroDivisionError)', Checker),
    (13, 10, 'DEAL021 raises contract error (KeyError)', Checker),
]


def test_stdin():
    checker = Checker(tree=ast.parse(TEXT))
    errors = list(checker.run())
    assert errors == EXPECTED


def test_astroid_path(tmp_path: Path):
    path = tmp_path / 'test.py'
    path.write_text(TEXT)
    checker = Checker(tree=ast.parse(TEXT), filename=str(path))
    errors = list(checker.run())
    assert errors == EXPECTED


def test_get_funcs_invalid_syntax(tmp_path: Path):
    """
    Atom IDE flake8 plugin can call flake8 with AST with correct syntax but with path
    to code with invalid syntax. In that case, we should ignore the file and fallback
    to the passed AST.
    """
    path = tmp_path / 'test.py'
    path.write_text('1/')
    checker = Checker(tree=ast.parse(TEXT), filename=str(path))
    errors = list(checker.run())
    assert errors == EXPECTED


def test_version():
    version = Checker(tree=None, filename='stdin').version
    assert not set(version) - set('0123456789.')


def test_remove_duplicates(tmp_path):
    text = """
        import deal

        def inner():
            raise TypeError
            raise TypeError

        @deal.raises()
        def outer():
            return inner()
    """
    path = tmp_path / 'test.py'
    path.write_text(dedent(text))
    checker = Checker(tree=ast.parse(TEXT), filename=str(path))
    errors = list(checker.run())
    assert len(errors) == 1
