from pathlib import Path
from textwrap import dedent

import deal
from sphinx.cmd.build import build_main


@deal.raises(ValueError, ZeroDivisionError)
def example():
    pass


def test_sphinx(tmp_path: Path):
    path_in = tmp_path / 'in'
    path_in.mkdir()
    path_out = tmp_path / 'out'
    (path_in / 'conf.py').write_text(dedent("""
        import deal

        def setup(app):
            deal.AutoDoc.Sphinx.register(app)
    """))
    (path_in / 'index.rst').write_text(dedent("""
        .. autofunction:: tests.test_sphinx.example
    """))
    exit_code = build_main([str(path_in), str(path_out), '-ET'])
    assert exit_code == 0
    content = (path_out / 'index.html').read_text()
    assert 'ValueError' in content
    assert 'ZeroDivisionError' in content
