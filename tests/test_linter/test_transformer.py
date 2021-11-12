from pathlib import Path
from textwrap import dedent
import pytest
from deal.linter import Transformer


@pytest.mark.parametrize('content', [
    # no-op
    """
        def f():
            return 1
        ---
        def f():
            return 1
    """,
    # preserve contracts
    """
        @deal.pre(lambda: True)
        def f():
            return 1
        ---
        @deal.pre(lambda: True)
        def f():
            return 1
    """,
    # add a new deal.raises
    """
        def f():
            raise ValueError
        ---
        @deal.raises(ValueError)
        def f():
            raise ValueError
    """,
    # remove deal.safe if adding deal.raises
    """
        @deal.safe
        def f():
            raise ValueError
        ---
        @deal.raises(ValueError)
        def f():
            raise ValueError
    """,
    # remove deal.pure if adding deal.raises
    """
        @deal.pure
        def f():
            raise ValueError
        ---
        @deal.raises(ValueError)
        @deal.has()
        def f():
            raise ValueError
    """,
    # merge deal.raises
    """
        @deal.raises(ZeroDivisionError)
        def f():
            raise ValueError
        ---
        @deal.raises(ZeroDivisionError, ValueError)
        def f():
            raise ValueError
    """,
])
def test_transformer(content: str, tmp_path: Path) -> None:
    given, expected = content.split('---')
    given = dedent(given)
    expected = dedent(expected)
    path = tmp_path / "example.py"
    path.write_text(given)
    tr = Transformer(path=path)
    actual = tr.transform()
    assert actual == expected
