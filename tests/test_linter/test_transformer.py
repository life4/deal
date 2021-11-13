from pathlib import Path
from textwrap import dedent
import pytest
from deal.linter import Transformer, TransformationType


@pytest.mark.parametrize('content', [
    # add deal.safe
    """
        def f():
            return 1
        ---
        @deal.safe
        def f():
            return 1
    """,
    # preserve deal.safe
    """
        @deal.safe
        def f():
            return 1
        ---
        @deal.safe
        def f():
            return 1
    """,
    # preserve deal.safe with comments
    """
        @deal.safe   # oh hi mark
        def f():
            return 1
        ---
        @deal.safe   # oh hi mark
        def f():
            return 1
    """,
    # preserve deal.raises
    """
        @deal.raises(KeyError)
        def f():
            return 1
        ---
        @deal.raises(KeyError)
        def f():
            return 1
    """,
    """
        @deal.raises(KeyError, UnknownError)
        def f():
            return 1
        ---
        @deal.raises(KeyError, UnknownError)
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
    # add deal.raises for unknown error
    """
        def f():
            raise UnknownError
        ---
        @deal.raises(UnknownError)
        def f():
            raise UnknownError
    """,
    # preserve unknown error
    """
        @deal.raises(UnknownError)
        def f():
            raise ValueError
        ---
        @deal.raises(UnknownError, ValueError)
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
    # preserve comments
    """
        # oh hi mark
        def f():
            raise ValueError
        ---
        # oh hi mark
        @deal.raises(ValueError)
        def f():
            raise ValueError
    """,
    # preserve comments
    """
        # oh hi mark

        def f():
            # hello
            raise ValueError
        ---
        # oh hi mark

        @deal.raises(ValueError)
        def f():
            # hello
            raise ValueError
    """,
    # preserve contracts
    """
        @deal.safe
        @deal.pre(lambda: True)
        def f():
            return 1
        ---
        @deal.safe
        @deal.pre(lambda: True)
        def f():
            return 1
    """,
    """
        @deal.pre(lambda: True)
        def f():
            return 1
        ---
        @deal.safe
        @deal.pre(lambda: True)
        def f():
            return 1
    """,
    """
        @deal.raises(ValueError)
        @deal.pre(lambda: True)
        def f():
            1/0
        ---
        @deal.raises(ValueError, ZeroDivisionError)
        @deal.pre(lambda: True)
        def f():
            1/0
    """,
])
def test_transformer_raises(content: str, tmp_path: Path) -> None:
    given, expected = content.split('---')
    given = dedent(given)
    expected = dedent(expected)
    tr = Transformer(
        content=given,
        path=tmp_path / "example.py",
        types={TransformationType.RAISES, TransformationType.SAFE},
    )
    actual = tr.transform()
    assert actual == expected


@pytest.mark.parametrize('content', [
    # add deal.has()
    """
        def f():
            return 1
        ---
        @deal.has()
        def f():
            return 1
    """,
    # add deal.has with markers
    """
        def f():
            print("hi")
            return 1
        ---
        @deal.has('stdout')
        def f():
            print("hi")
            return 1
    """,
    """
        import random
        def f():
            print(random.choice([1,2]))
            return 1
        ---
        import random
        @deal.has('random', 'stdout')
        def f():
            print(random.choice([1,2]))
            return 1
    """,
    # merge deal.has
    """
        @deal.has('random')
        def f():
            print("hi")
            return 1
        ---
        @deal.has('random', 'stdout')
        def f():
            print("hi")
            return 1
    """,
    """
        @deal.has()
        def f():
            print("hi")
            return 1
        ---
        @deal.has('stdout')
        def f():
            print("hi")
            return 1
    """,
    # replace deal.pure
    """
        @deal.pure
        def f():
            print("hi")
            return 1
        ---
        @deal.has('stdout')
        @deal.safe
        def f():
            print("hi")
            return 1
    """,
    # preserve contracts
    """
        @deal.pre(lambda: True)
        def f():
            print("hi")
            return 1
        ---
        @deal.has('stdout')
        @deal.pre(lambda: True)
        def f():
            print("hi")
            return 1
    """,
    """
        @deal.has('random')
        def f():
            return 1
        ---
        @deal.has('random')
        def f():
            return 1
    """,
    """
        @deal.has('random')
        @deal.pre(lambda: True)
        def f():
            return 1
        ---
        @deal.has('random')
        @deal.pre(lambda: True)
        def f():
            return 1
    """,
    """
        @deal.has()
        @deal.pre(lambda: True)
        def f():
            return 1
        ---
        @deal.has()
        @deal.pre(lambda: True)
        def f():
            return 1
    """,
    """
        @deal.pre(lambda: True)
        def f():
            return 1
        ---
        @deal.has()
        @deal.pre(lambda: True)
        def f():
            return 1
    """,
    # do not add deal.raises if transformation type is disabled
    """
        def f():
            raise ValueError
            return 1
        ---
        @deal.has()
        def f():
            raise ValueError
            return 1
    """,
])
def test_transformer_has(content: str, tmp_path: Path) -> None:
    given, expected = content.split('---')
    given = dedent(given)
    expected = dedent(expected)
    tr = Transformer(
        content=given,
        path=tmp_path / "example.py",
        types={TransformationType.HAS},
    )
    actual = tr.transform()
    assert actual == expected
