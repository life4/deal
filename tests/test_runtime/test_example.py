from asyncio import iscoroutinefunction
from inspect import isgeneratorfunction

import deal

from .helpers import run_sync


def test_example_is_not_triggered_in_runtime():
    @deal.example(lambda: False)
    @deal.example(lambda: 1 / 0 == 0)
    def f1() -> bool:
        return True

    assert f1() is True


def test_example_does_not_break_iterator():
    @deal.example(lambda: False)
    @deal.example(lambda: 1 / 0 == 0)
    def f1():
        yield True

    assert isgeneratorfunction(f1) is True
    assert next(f1()) is True
    assert list(f1()) == [True]


def test_example_does_not_break_async():
    @deal.example(lambda: False)
    @deal.example(lambda: 1 / 0 == 0)
    async def f1() -> bool:
        return True

    assert iscoroutinefunction(f1) is True
    assert run_sync(f1()) is True
