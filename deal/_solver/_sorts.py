import z3
from ._exceptions import UnsupportedError


def unwrap(obj) -> z3.Z3PPObject:
    if isinstance(obj, ProxySort):
        return obj.expr
    return obj


def wrap(expr):
    if z3.is_string(expr):
        return StrSort(expr=expr)
    if z3.is_seq(expr):
        return ListSort(expr=expr)
    if z3.is_array(expr):
        return SetSort(expr=expr)
    return expr


class ProxySort:
    expr: z3.Z3PPObject

    def _ensure(self, item):
        pass

    def __init__(self, expr) -> None:
        self.expr = expr

    def __eq__(self, other):
        self._ensure(other)
        return unwrap(self) == unwrap(other)

    def __ne__(self, other):
        self._ensure(other)
        return unwrap(self) != unwrap(other)

    def __lt__(self, other):
        self._ensure(other)
        return unwrap(self) < unwrap(other)

    def __le__(self, other):
        self._ensure(other)
        return unwrap(self) <= unwrap(other)

    def __gt__(self, other):
        self._ensure(other)
        return unwrap(self) > unwrap(other)

    def __ge__(self, other):
        self._ensure(other)
        return unwrap(self) >= unwrap(other)

    def __add__(self, other):
        self._ensure(other)
        cls = type(self)
        return cls(expr=unwrap(self) + unwrap(other))


class SeqSort(ProxySort):
    expr: z3.SeqRef

    @classmethod
    def make_empty(cls, sort: z3.SortRef = None) -> 'SeqSort':
        expr = None
        if sort is not None:
            expr = z3.Empty(z3.SeqSort(sort))
        return cls(expr=expr)

    def _ensure(self, item):
        if self.expr is not None:
            return
        sort = item.sort()
        # if isinstance(sort, z3.SeqSortRef):
        #     import pdb
        #     pdb.set_trace()
        self.expr = z3.Empty(z3.SeqSort(sort))

    def append(self, item: z3.ExprRef) -> 'SeqSort':
        cls = type(self)
        unit = z3.Unit(unwrap(item))
        self._ensure(item)
        return cls(expr=self.expr + unit)

    def length(self) -> z3.ArithRef:
        if self.expr is None:
            return z3.IntVal(0)
        return z3.Length(self.expr)

    def __bool__(self):
        if self.expr is None:
            return z3.BoolVal(False)
        return z3.Length(self.expr) == z3.IntVal(0)


class ListSort(SeqSort):
    def contains(self, item):
        self._ensure(item)
        unit = z3.Unit(unwrap(item))
        return z3.Contains(self.expr, unit)


class StrSort(SeqSort):
    @classmethod
    def convert(cls, obj):
        if z3.is_int(obj):
            return cls(expr=z3.IntToStr(obj))
        raise UnsupportedError('cannot convert', obj, 'to str')

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


class SetSort(ProxySort):
    def _ensure(self, item):
        if self.expr is not None:
            return
        sort = item.sort()
        # if isinstance(sort, z3.SeqSortRef):
        #     import pdb
        #     pdb.set_trace()
        self.expr = z3.EmptySet(sort)

    @classmethod
    def make_empty(cls, sort: z3.SortRef = None) -> 'SetSort':
        expr = None
        if sort is not None:
            expr = z3.EmptySet(sort)
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
