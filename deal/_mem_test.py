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

    def __exit__(self, *exc) -> None:
        self.after = self._dump()
        if 'diff' in vars(self):
            del vars(self)['diff']

    @cached_property
    def diff(self) -> typing.Counter[str]:
        return self.after - self.before

    @classmethod
    def _dump(cls) -> typing.Counter[str]:
        counter = Counter()
        gc.collect()
        for obj in gc.get_objects():
            name = cls._get_type_name(obj)
            counter[name] += 1
        return counter

    @staticmethod
    def _get_type_name(obj) -> str:
        t = type(obj)
        if hasattr(t, '__qualname__'):
            return t.__qualname__
        if hasattr(t, '__name__'):
            return t.__name__
        return repr(t)
