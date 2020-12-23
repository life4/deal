import z3
from ._proxy import ProxySort
from ._funcs import unwrap
from ._registry import registry


@registry.add
class SetSort(ProxySort):
    type_name = 'set'

    @staticmethod
    def make_empty_expr(sort):
        return z3.EmptySet(sort)

    @classmethod
    def make_empty(cls, sort: z3.SortRef = None) -> 'SetSort':
        expr = None
        if sort is not None:
            expr = cls.make_empty_expr(sort)
        return cls(expr=expr)

    def add(self, item: z3.ExprRef) -> 'SetSort':
        self._ensure(item)
        cls = type(self)
        return cls(
            expr=z3.SetAdd(s=self.expr, e=unwrap(item)),
        )

    def contains(self, item):
        self._ensure(item)
        return z3.IsMember(e=unwrap(item), s=self.expr)
