import typing
import z3


class Scope:
    _vars: typing.Dict[str, z3.Z3PPObject]

    def __init__(self, vars) -> None:
        self._vars = vars

    @classmethod
    def make_empty(cls) -> 'Scope':
        return cls(vars=dict())

    def get(self, name: str) -> typing.Optional[z3.Z3PPObject]:
        return self._vars.get(name)

    def set(self, name: str, var: z3.Z3PPObject) -> None:
        self._vars[name] = var


class Context(typing.NamedTuple):
    z3_ctx: typing.Optional[z3.Context]
    scope: Scope

    @classmethod
    def make_empty(cls) -> 'Context':
        return cls(
            z3_ctx=None,
            scope=Scope.make_empty(),
        )
