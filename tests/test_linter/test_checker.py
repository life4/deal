import ast
import subprocess
import sys
from pathlib import Path
from textwrap import dedent

import pytest

from deal.linter import Checker


try:
    import astroid
except ImportError:
    astroid = None

try:
    import flake8
except ImportError:
    flake8 = None


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
    checker = Checker.from_path(path)
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
    version = Checker(tree=None, filename='stdin').version  # type: ignore[arg-type]
    assert version.count('.') == 2
    assert not set(version) - set('0123456789.')


@pytest.mark.skipif(astroid is None, reason='astroid is not installed')
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
    checker = Checker.from_path(path)
    errors = list(checker.run())
    assert len(errors) == 1


@pytest.mark.skipif(flake8 is None, reason='flake8 is not installed')
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


@pytest.mark.parametrize('comment, should_fail', [
    ('', True),

    # different prefix sizes
    ('# noqa: DEAL021', False),
    ('# noqa: DEAL02', False),
    ('# noqa: DEAL0', False),
    ('# noqa: DEAL', False),

    # case insensitive
    ('# NoQA: DEAL', False),
    ('# NOQA: DEAL', False),
    ('# noqa: deal', False),

    # aliases
    ('# noqa: DEA021', False),
    ('# noqa: DEL021', False),
    ('# noqa: DIL021', False),
    ('# noqa: DEA0', False),
    ('# noqa: DEA', False),

    # mixed with other codes and garbage
    ('# noqa: W13, DEAL021', False),
    ('# noqa: DEAL021, W13', False),
    ('# noqa: DEAL021 # nosec # type: ignore', False),
    ('# nosec # type: ignore # noqa: DEAL021', False),

    # not this noqa
    ('# noqa: W13', True),
    ('# noqa: DEAL022', True),
    ('# noqa: D022', True),
    ('# oh hi mark', True),
    ('# type: ignore', True),
    ('# nosec', True),
])
def test_noqa(tmp_path: Path, comment, should_fail):
    text = f"""
        import deal
        @deal.safe
        def f():
            1/0 {comment}
    """
    path = tmp_path / 'test.py'
    path.write_text(dedent(text))
    checker = Checker.from_path(path)
    errors = list(checker.run())
    assert len(errors) == int(should_fail)
