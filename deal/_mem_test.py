import gc
import typing
from collections import Counter

from ._cached_property import cached_property


class MemoryTracker:
    before: typing.Counter[str]
    after: typing.Counter[str]

    def __init__(self) -> None:
        self.before = Counter()
        self.after = Counter()

    def __enter__(self) -> None:
        self.before = self._dump()

    def __exit__(self, *exc) -> None:
        self.after = self._dump()

    @cached_property
    def diff(self) -> typing.Counter[str]:
        return self.after - self.before - Counter({'weakref': 1})

    @staticmethod
    def _dump() -> typing.Counter[str]:
        counter: typing.Counter[str] = Counter()
        gc.collect()
        for obj in gc.get_objects():
            name: str = type(obj).__qualname__
            counter[name] += 1
        return counter
