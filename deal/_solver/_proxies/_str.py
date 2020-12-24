import z3
from .._exceptions import UnsupportedError
from ._proxy import ProxySort
from ._funcs import unwrap
from ._registry import registry


@registry.add
class StrSort(ProxySort):
    type_name = 'str'

    @staticmethod
    def make_empty_expr(sort=None):
        return z3.Empty(z3.StringSort())

    def _ensure(self, item, seq=False):
        pass

    @classmethod
    def make_empty(cls, sort: z3.SortRef = None) -> 'StrSort':
        expr = cls.make_empty_expr(sort)
        return cls(expr=expr)

    @property
    def as_int(self):
        int_proxy = registry['int']
        return int_proxy(expr=z3.StrToInt(self.expr))

    @property
    def as_str(self):
        return self

    @property
    def as_float(self):
        float_proxy = registry['float']
        if z3.is_string_value(self.expr):
            val = float(self.expr.as_string())
            return float_proxy.val(val)
        raise UnsupportedError('cannot convert str to float')

    def contains(self, item):
        self._ensure(item)
        return z3.Contains(self.expr, unwrap(item))

    def startswith(self, prefix):
        if self.expr is None:
            return z3.BoolVal(False)
        return z3.PrefixOf(unwrap(prefix), self.expr)

    def endswith(self, suffix):
        if self.expr is None:
            return z3.BoolVal(False)
        return z3.SuffixOf(unwrap(suffix), self.expr)

    def index(self, other, start=None):
        if start is None:
            start = z3.IntVal(0)
        return z3.IndexOf(self.expr, unwrap(other), start)

    def length(self) -> z3.ArithRef:
        if self.expr is None:
            return z3.IntVal(0)
        return z3.Length(self.expr)
