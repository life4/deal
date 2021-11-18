from io import StringIO
from pathlib import Path
from textwrap import dedent

import pytest

from deal._cli import main


@pytest.mark.parametrize('flags, given, expected', [
    (
        [],
        """
            @deal.post(lambda x: x > 0)
            def f(x):
                print(1/0)
                return -1
        """,
        """
            import deal

            @deal.has('stdout')
            @deal.raises(ZeroDivisionError)
            @deal.post(lambda x: x > 0)
            def f(x):
                print(1/0)
                return -1
        """,
    ),
    (
        ['--types', 'raises', 'safe'],
        """
            import deal
            @deal.post(lambda x: x > 0)
            def f(x):
                print(1/0)
                return -1
        """,
        """
            import deal
            @deal.raises(ZeroDivisionError)
            @deal.post(lambda x: x > 0)
            def f(x):
                print(1/0)
                return -1
        """,
    ),
    (
        ['--types', 'has', '--double-quotes'],
        """
            import deal
            @deal.post(lambda x: x > 0)
            def f(x):
                print(1/0)
                return -1
        """,
        """
            import deal
            @deal.has("stdout")
            @deal.post(lambda x: x > 0)
            def f(x):
                print(1/0)
                return -1
        """,
    ),
    (
        [],
        """
            import deal
            @deal.pure
            def f(x):
                return x
        """,
        """
            import deal
            @deal.pure
            def f(x):
                return x
        """,
    ),
])
def test_decorate_command(flags: list, given: str, expected: str, tmp_path: Path):
    file_path = tmp_path / 'example.py'
    file_path.write_text(dedent(given))
    stream = StringIO()
    code = main(['decorate', *flags, '--', str(tmp_path)], stream=stream)
    assert code == 0

    stream.seek(0)
    captured = stream.read()
    assert str(file_path) in captured
    assert file_path.read_text().lstrip('\n') == dedent(expected).lstrip('\n')
