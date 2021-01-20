# external
import z3

# app
from ._funcs import random_name, unwrap, wrap
from ._proxy import ProxySort
from ._registry import registry


@registry.add
class ListSort(ProxySort):
    expr: z3.SeqRef
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
        return z3.Length(self.expr) != z3.IntVal(0)

    def get_item(self, index):
        return wrap(self.expr[unwrap(index)])

    def get_slice(self, start, stop):
        if self.expr is None:
            return self
        start = unwrap(start)
        stop = unwrap(stop)
        return wrap(z3.SubSeq(
            s=self.expr,
            offset=start,
            length=stop - start,
        ))

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

    @property
    def length(self):
        int_proxy = registry['int']
        if self.expr is None:
            return int_proxy(expr=z3.IntVal(0))
        return int_proxy(expr=z3.Length(self.expr))

    def count(self, item):
        if self.expr is None:
            int_proxy = registry['int']
            return int_proxy(expr=z3.IntVal(0))
        item = unwrap(item)
        f = z3.RecFunction(
            random_name('list_count'),
            z3.IntSort(), z3.IntSort(),
        )
        i = z3.Int(random_name('index'))
        one = z3.IntVal(1)
        zero = z3.IntVal(0)
        z3.RecAddDefinition(f, i, z3.If(
            i < zero,
            zero,
            f(i - one) + z3.If(self.expr[i] == item, one, zero),
        ))
        result = f(z3.Length(self.expr) - one)
        return wrap(result)
