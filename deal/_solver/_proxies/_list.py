import z3
from ._funcs import unwrap
from ._proxy import ProxySort
from ._registry import registry


@registry.add
class ListSort(ProxySort):
    type_name = 'list'

    @classmethod
    def make_empty(cls, sort: z3.SortRef = None) -> 'ListSort':
        expr = None
        if sort is not None:
            expr = cls.make_empty_expr(sort)
        return cls(expr=expr)

    @staticmethod
    def make_empty_expr(sort):
        return z3.Empty(z3.SeqSort(sort))

    @property
    def as_bool(self):
        if self.expr is None:
            return z3.BoolVal(False)
        return z3.Length(self.expr) == z3.IntVal(0)

    def append(self, item: z3.ExprRef) -> 'ListSort':
        cls = type(self)
        unit = z3.Unit(unwrap(item))
        self._ensure(item)
        return cls(expr=self.expr + unit)

    def contains(self, item):
        self._ensure(item)
        unit = z3.Unit(unwrap(item))
        return z3.Contains(self.expr, unit)

    def index(self, other, start=None):
        if start is None:
            start = z3.IntVal(0)
        unit = z3.Unit(unwrap(other))
        int_proxy = registry['int']
        return int_proxy(expr=z3.IndexOf(self.expr, unit, start))

    def length(self) -> z3.ArithRef:
        int_proxy = registry['int']
        if self.expr is None:
            return int_proxy(expr=z3.IntVal(0))
        return int_proxy(expr=z3.Length(self.expr))
