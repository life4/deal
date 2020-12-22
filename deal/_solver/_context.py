import typing
from collections import Counter
from contextlib import contextmanager

import z3


class Asserts:
    _asserts: typing.List[z3.BoolRef]

    def __init__(self) -> None:
        self._asserts = []

    def add(self, cond: z3.BoolRef) -> None:
        self._asserts.append(cond)

    def __iter__(self):
        return iter(self._asserts)

    def __repr__(self) -> str:
        return '{n}({r})'.format(
            n=type(self).__name__,
            r=repr(self._asserts),
        )


class Scope:
    _parent: typing.Optional['Scope']
    layer: typing.Dict[str, z3.Z3PPObject]

    def __init__(self, parent: 'Scope', vars) -> None:
        self._parent = parent
        self.layer = vars

    @classmethod
    def make_empty(cls) -> 'Scope':
        return cls(
            vars=dict(),
            parent=None,
        )

    def make_child(self) -> 'Scope':
        cls = type(self)
        return cls(
            parent=self,
            vars=dict(),
        )

    def get(self, name: str) -> typing.Optional[z3.Z3PPObject]:
        var = self.layer.get(name)
        if var is not None:
            return var
        if self._parent is not None:
            return self._parent.get(name=name)
        return None

    def set(self, name: str, value: z3.Z3PPObject) -> None:
        self.layer[name] = value

    def __repr__(self) -> str:
        return '{n}({r})'.format(
            n=type(self).__name__,
            r=repr(self.layer),
        )


class Trace:
    __slots__ = ['_names']
    _names: Counter

    def __init__(self) -> None:
        self._names = Counter()

    @contextmanager
    def guard(self, name: str) -> None:
        self._names[name] += 1
        try:
            yield
        finally:
            self._names[name] -= 1

    def __contains__(self, name: str) -> bool:
        return self._names[name] > 0

    def __repr__(self) -> str:
        return '{n}({r})'.format(
            n=type(self).__name__,
            r=', '.join(sorted(self._names)),
        )


class Context(typing.NamedTuple):
    z3_ctx: typing.Optional[z3.Context]
    scope: Scope
    given: Asserts
    expected: Asserts
    trace: Trace

    @classmethod
    def make_empty(cls) -> 'Context':
        return cls(
            z3_ctx=None,
            scope=Scope.make_empty(),
            given=Asserts(),
            expected=Asserts(),
            trace=Trace(),
        )

    @property
    def evolve(self) -> typing.Callable[..., 'Context']:
        return self._replace

    def make_child(self) -> 'Context':
        return self.evolve(scope=self.scope.make_child())
