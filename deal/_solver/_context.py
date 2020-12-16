import typing
import z3


class Scope:
    _vars: typing.Dict[str, z3.SortRef]

    def __init__(self, vars) -> None:
        self._vars = vars

    @classmethod
    def make_empty(cls) -> 'Scope':
        return cls(vars=dict())


class Context(typing.NamedTuple):
    z3_ctx: typing.Optional[z3.Context]
    scope: Scope

    @classmethod
    def make_empty(cls) -> 'Context':
        return cls(
            z3_ctx=None,
            scope=Scope.make_empty(),
        )
