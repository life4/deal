import z3
from ._exceptions import UnsupportedError


def unwrap(obj) -> z3.Z3PPObject:
    if not isinstance(obj, ProxySort):
        return obj
    expr = obj.expr
    if expr is None:
        return obj.make_empty_expr(z3.IntSort())
    return expr


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

    @staticmethod
    def make_empty_expr():
        raise NotImplementedError

    def _ensure(self, item, seq=False):
        """
        Sometimes, the subtype for sequences is not known in advance.
        In that case, we set `expr=None`.

        What `_ensure` does is it takes another item or sequence,
        extracts type from it, and sets the type for the current sequence
        to match the another one. For example, if `a` is an empty list,
        operation `a.append(1)` will set the subtype of `a` to `int`.
        """
        if self.expr is not None:
            return
        item = unwrap(item)
        if item is None:
            sort = z3.IntSort()
        else:
            sort = item.sort()

        if seq:
            if isinstance(sort, z3.ArraySortRef):
                sort = sort.domain()
            elif isinstance(sort, z3.SeqSortRef):
                sort = sort.basis()

        self.expr = self.make_empty_expr(sort)

    def __init__(self, expr) -> None:
        self.expr = expr

    def __eq__(self, other):
        self._ensure(other, seq=True)
        return unwrap(self) == unwrap(other)

    def __ne__(self, other):
        self._ensure(other, seq=True)
        return unwrap(self) != unwrap(other)

    def __lt__(self, other):
        self._ensure(other, seq=True)
        return unwrap(self) < unwrap(other)

    def __le__(self, other):
        self._ensure(other, seq=True)
        return unwrap(self) <= unwrap(other)

    def __gt__(self, other):
        self._ensure(other, seq=True)
        return unwrap(self) > unwrap(other)

    def __ge__(self, other):
        self._ensure(other, seq=True)
        return unwrap(self) >= unwrap(other)

    def __add__(self, other):
        self._ensure(other, seq=True)
        cls = type(self)
        return cls(expr=unwrap(self) + unwrap(other))


class SeqSort(ProxySort):
    expr: z3.SeqRef

    @staticmethod
    def make_empty_expr(sort):
        return z3.Empty(z3.SeqSort(sort))

    @classmethod
    def make_empty(cls, sort: z3.SortRef = None) -> 'SeqSort':
        expr = None
        if sort is not None:
            expr = cls.make_empty_expr(sort)
        return cls(expr=expr)

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
