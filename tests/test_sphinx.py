from pathlib import Path
from textwrap import dedent

import pytest
from sphinx.cmd.build import build_main

import deal


contracts = deal.chain(
    deal.reason(ZeroDivisionError, lambda a, b: b == 0),
    deal.reason(ValueError, lambda a, b: a == b, message='a is equal to b'),
    deal.raises(ValueError, IndexError, ZeroDivisionError),
    deal.post(lambda res: res != .13),
    deal.ensure(lambda a, b, result: b != result),
    deal.pre(lambda a, b: b != 0, message='b is not zero'),
    deal.pre(lambda a, b: b != 0),
    deal.has('database'),
)


@contracts
@deal.example(lambda: example_sphinx(6, 2) == 3)
def example_sphinx(a: int, b: int) -> float:
    """Example function.

    :return: The description for return value.
    """
    return a / b


@contracts
@deal.example(lambda: example_google(6, 2) == 3)
def example_google(a: int, b: int) -> float:
    """Example function.

    Returns:
        The description for return value.
    """
    return a / b


def example_plain(a: int, b: int) -> float:
    """Example function.

    Returns:
        The description for return value.
    """
    return a / b


CONFIG = """
    import deal

    extensions = [
        'sphinx.ext.autodoc',
        'sphinx.ext.napoleon',
    ]

    def setup(app):
        deal.autodoc(app)
"""


@pytest.mark.parametrize('style', ['sphinx', 'google'])
def test_autodoc_smoke(style: str, tmp_path: Path):
    path_in = tmp_path / 'in'
    path_in.mkdir()
    path_out = tmp_path / 'out'
    (path_in / 'conf.py').write_text(dedent(CONFIG))
    (path_in / 'index.rst').write_text(dedent(f"""
        .. autofunction:: tests.test_sphinx.example_{style}
    """))
    exit_code = build_main([str(path_in), str(path_out), '-b', 'text', '-ET'])
    assert exit_code == 0
    content = (path_out / 'index.txt').read_text()
    assert 'ValueError' in content
    assert 'ZeroDivisionError' in content
    assert 'b == 0' in content

    expected = dedent(f"""
        tests.test_sphinx.example_{style}(a: int, b: int) -> float
            Example function.
            Returns:
                The description for return value.
            Side-effects:
                * database
            Raises:
                * **IndexError** --
                * **ValueError** -- a is equal to b
                * **ZeroDivisionError** -- "b == 0"
            Contracts:
                * b is not zero
                * "b != 0"
                * "res != .13"
                * "b != result"
            Examples:
                * "example_{style}(6, 2) == 3"
    """)

    lines = [line.strip() for line in content.splitlines()]
    content = '\n'.join(line for line in lines if line)

    lines = [line.strip() for line in expected.splitlines()]
    expected = '\n'.join(line for line in lines if line)

    assert content.strip() == expected.strip()


def test_autodoc_no_contracts(tmp_path: Path):
    path_in = tmp_path / 'in'
    path_in.mkdir()
    path_out = tmp_path / 'out'
    (path_in / 'conf.py').write_text(dedent(CONFIG))
    (path_in / 'index.rst').write_text(
        '.. autofunction:: tests.test_sphinx.example_plain',
    )
    exit_code = build_main([str(path_in), str(path_out), '-b', 'text', '-ET'])
    assert exit_code == 0
    content = (path_out / 'index.txt').read_text()
    assert 'tests.test_sphinx.example_plain' in content
    assert 'Contracts' not in content
