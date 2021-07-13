from pathlib import Path
from textwrap import dedent

import pytest
import deal
from sphinx.cmd.build import build_main


@deal.reason(ZeroDivisionError, lambda a, b: b == 0)
@deal.reason(ValueError, lambda a, b: a == b, message='a is equal to b')
@deal.raises(ValueError, IndexError, ZeroDivisionError)
@deal.pre(lambda a, b: b != 0)
@deal.pre(lambda a, b: b != 0, message="b is not zero")
@deal.ensure(lambda a, b, result: b != result)
@deal.post(lambda res: res != .13)
def example_sphinx(a: int, b: int) -> float:
    """Example function.

    :return: The description for return value.
    """
    return a / b


@deal.reason(ZeroDivisionError, lambda a, b: b == 0)
@deal.reason(ValueError, lambda a, b: a == b, message='a is equal to b')
@deal.raises(ValueError, IndexError, ZeroDivisionError)
@deal.pre(lambda a, b: b != 0)
@deal.pre(lambda a, b: b != 0, message="b is not zero")
@deal.ensure(lambda a, b, result: b != result)
@deal.post(lambda res: res != .13)
def example_google(a: int, b: int) -> float:
    """Example function.

    Returns:
        The description for return value.
    """
    return a / b


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
    assert 'b == 0' in content

    expected = dedent(f"""
        tests.test_sphinx.example_{style.lower()}(a: int, b: int) -> float
            Example function.
            Returns:
                The description for return value.
            Raises:
                * **IndexError** --
                * **ValueError** -- a is equal to b
                * **ZeroDivisionError** -- "b == 0"
            Contracts:
                * "b != 0"
                * b is not zero
                * "b != result"
                * "res != .13"
    """)
    content = '\n'.join([line.strip() for line in content.splitlines() if line.strip()])
    expected = '\n'.join([line.strip() for line in expected.splitlines() if line.strip()])
    assert content.strip() == expected.strip()
