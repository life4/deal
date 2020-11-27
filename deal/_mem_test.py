import gc
import typing
from collections import Counter
from._cached_property import cached_property


class MemoryTracker:
    before: typing.Counter[str]
    after: typing.Counter[str]

    def __init__(self) -> None:
        self.before = Counter()
        self.after = Counter()

    def __enter__(self) -> None:
        self.before = self._dump()

    def __exit__(self, *exc) -> bool:
        self.after = self._dump()
        return False

    @cached_property
    def diff(self) -> typing.Counter[str]:
        return self.after - self.before - Counter({'weakref': 1})

    @classmethod
    def _dump(cls) -> typing.Counter[str]:
        counter: typing.Counter[str] = Counter()
        gc.collect()
        for obj in gc.get_objects():
            name: str = type(obj).__qualname__
            counter[name] += 1
        return counter
