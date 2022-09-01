import ast
from pathlib import Path
import subprocess
import sys
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
    (6, 11, 'DEL012 post contract error (-1)', Checker),
    (11, 8, 'DEL021 raises contract error (ZeroDivisionError)', Checker),
    (13, 10, 'DEL021 raises contract error (KeyError)', Checker),
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
    version = Checker.version
    assert len(version) >= 5
    assert not set(version) - set('0123456789.')


def test_remove_duplicates(tmp_path: Path):
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


def test_flake8_integration(tmp_path: Path):
    path = tmp_path / 'test.py'
    path.write_text(TEXT + '\n')
    cmd = [sys.executable, '-m', 'flake8', str(tmp_path)]
    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    assert result.returncode == 1
    lines = result.stdout.decode().splitlines()
    assert len(EXPECTED) == len(lines), result.stderr
    for (lineno, col, error, _), line in zip(EXPECTED, lines):
        assert error in line
        assert f':{lineno}:{col + 1}' in line
