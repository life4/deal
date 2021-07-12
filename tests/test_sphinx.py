from pathlib import Path
from textwrap import dedent

import pytest
import deal
from sphinx.cmd.build import build_main


@deal.raises(ValueError, ZeroDivisionError)
def example_sphinx():
    """Example function.

    :return: The return value. True for success, False otherwise.
    :rtype: bool
    """
    return True


@deal.raises(ValueError, ZeroDivisionError)
def example_google():
    """Example function.

    Returns:
        bool: The return value. True for success, False otherwise.
    """
    return True


@pytest.mark.parametrize('style', ['Sphinx', 'Google'])
def test_autodoc_smoke(style: str, tmp_path: Path):
    path_in = tmp_path / 'in'
    path_in.mkdir()
    path_out = tmp_path / 'out'
    (path_in / 'conf.py').write_text(dedent(f"""
        import deal

        def setup(app):
            deal.AutoDoc.{style}.register(app)
    """))
    (path_in / 'index.rst').write_text(dedent(f"""
        .. autofunction:: tests.test_sphinx.example_{style.lower()}
    """))
    exit_code = build_main([str(path_in), str(path_out), '-b', 'text', '-ET'])
    assert exit_code == 0
    content = (path_out / 'index.txt').read_text()
    assert 'ValueError' in content
    assert 'ZeroDivisionError' in content


@pytest.mark.parametrize('style, expected', [
    (
        'Sphinx',
        """
        tests.test_sphinx.example_sphinx()
           Example function.
           Returns:
                The return value. True for success, False otherwise.
           Return type:
                bool
           Raises:
                * **ValueError** --
                * **ZeroDivisionError** --
        """,
    ),
    (
        'Google',
        """
        tests.test_sphinx.example_google()
            Example function.
            Returns:
                The return value. True for success, False otherwise.
            Return type:
                bool
            Raises:
                ValueError ZeroDivisionError
        """,
    ),
])
def test_autodoc_exact_match(style: str, expected: str, tmp_path: Path):
    path_in = tmp_path / 'in'
    path_in.mkdir()
    path_out = tmp_path / 'out'
    (path_in / 'conf.py').write_text(dedent(f"""
        import deal

        def setup(app):
            deal.AutoDoc.{style}.register(app)
    """))
    (path_in / 'index.rst').write_text(dedent(f"""
        .. autofunction:: tests.test_sphinx.example_{style.lower()}
    """))
    exit_code = build_main([str(path_in), str(path_out), '-b', 'text', '-ET'])
    assert exit_code == 0
    content = (path_out / 'index.txt').read_text()
    content = '\n'.join([line.strip() for line in content.splitlines() if line.strip()])
    expected = '\n'.join([line.strip() for line in expected.splitlines() if line.strip()])
    assert content.strip() == expected.strip()
