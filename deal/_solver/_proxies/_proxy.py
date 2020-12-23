import z3
from ._funcs import unwrap


class ProxySort:
    type_name: str
    expr: z3.Z3PPObject

    @staticmethod
    def make_empty_expr():
        raise NotImplementedError

    def _ensure(self, item, seq=False) -> None:
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

    # comparison

    def __eq__(self, other):
        self._ensure(other, seq=True)
        return self.expr == unwrap(other)

    def __ne__(self, other):
        self._ensure(other, seq=True)
        return self.expr != unwrap(other)

    def __lt__(self, other):
        self._ensure(other, seq=True)
        return self.expr < unwrap(other)

    def __le__(self, other):
        self._ensure(other, seq=True)
        return self.expr <= unwrap(other)

    def __gt__(self, other):
        self._ensure(other, seq=True)
        return self.expr > unwrap(other)

    def __ge__(self, other):
        self._ensure(other, seq=True)
        return self.expr >= unwrap(other)

    # unary operations

    def __neg__(self):
        cls = type(self)
        return cls(expr=-self.expr)

    def __pos__(self):
        cls = type(self)
        return cls(expr=+self.expr)

    def __inv__(self):
        cls = type(self)
        return cls(expr=~self.expr)

    # binary operations

    def __add__(self, other):
        self._ensure(other, seq=True)
        cls = type(self)
        return cls(expr=self.expr + unwrap(other))

    def __sub__(self, other):
        self._ensure(other, seq=True)
        cls = type(self)
        return cls(expr=self.expr - unwrap(other))

    def __mul__(self, other):
        self._ensure(other, seq=True)
        cls = type(self)
        return cls(expr=self.expr * unwrap(other))

    def __truediv__(self, other):
        self._ensure(other, seq=True)
        cls = type(self)
        return cls(expr=self.expr / unwrap(other))

    def __floordiv__(self, other):
        self._ensure(other, seq=True)
        cls = type(self)
        return cls(expr=self.expr // unwrap(other))

    def __mod__(self, other):
        self._ensure(other, seq=True)
        cls = type(self)
        return cls(expr=self.expr % unwrap(other))

    def __pow__(self, other):
        self._ensure(other, seq=True)
        cls = type(self)
        return cls(expr=self.expr ** unwrap(other))

    def __matmul__(self, other):
        self._ensure(other, seq=True)
        cls = type(self)
        return cls(expr=self.expr @ unwrap(other))
