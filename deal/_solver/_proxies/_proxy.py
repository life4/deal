import operator

import z3

from ._funcs import unwrap
from .._exceptions import UnsupportedError


class ProxySort:
    type_name: str
    expr: z3.Z3PPObject

    @staticmethod
    def make_empty_expr(sort):
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

    # abstract methods

    @property
    def as_bool(self):
        raise UnsupportedError('cannot convert {} to bool'.format(self.type_name))

    @property
    def as_int(self):
        raise UnsupportedError('cannot convert {} to int'.format(self.type_name))

    def _binary_op(self, other, handler):
        self._ensure(other, seq=True)
        return handler(self.expr, unwrap(other))

    # comparison

    def _comp_op(self, other, handler):
        return self._binary_op(other=other, handler=handler)

    def __eq__(self, other):
        return self._comp_op(other=other, handler=operator.__eq__)

    def __ne__(self, other):
        return self._comp_op(other=other, handler=operator.__ne__)

    def __lt__(self, other):
        return self._comp_op(other=other, handler=operator.__lt__)

    def __le__(self, other):
        return self._comp_op(other=other, handler=operator.__le__)

    def __gt__(self, other):
        return self._comp_op(other=other, handler=operator.__gt__)

    def __ge__(self, other):
        return self._comp_op(other=other, handler=operator.__ge__)

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

    # math binary operations

    def _math_op(self, other, handler):
        cls = type(self)
        expr = self._binary_op(other=other, handler=handler)
        return cls(expr=expr)

    def __add__(self, other):
        return self._math_op(other=other, handler=operator.__add__)

    def __sub__(self, other):
        return self._math_op(other=other, handler=operator.__sub__)

    def __mul__(self, other):
        return self._math_op(other=other, handler=operator.__mul__)

    def __truediv__(self, other):
        return self._math_op(other=other, handler=operator.__truediv__)

    def __floordiv__(self, other):
        return self._math_op(other=other, handler=operator.__floordiv__)

    def __mod__(self, other):
        return self._math_op(other=other, handler=operator.__mod__)

    def __pow__(self, other):
        return self._math_op(other=other, handler=operator.__pow__)

    def __matmul__(self, other):
        return self._math_op(other=other, handler=operator.__matmul__)

    # bitwise binary operations

    def _bitwise_op(self, other, handler):
        cls = type(self)
        expr = self._binary_op(other=other, handler=handler)
        return cls(expr=expr)

    def __and__(self, other):
        return self._bitwise_op(other=other, handler=operator.__and__)

    def __or__(self, other):
        return self._bitwise_op(other=other, handler=operator.__or__)

    def __xor__(self, other):
        return self._bitwise_op(other=other, handler=operator.__xor__)

    def __lshift__(self, other):
        return self._bitwise_op(other=other, handler=operator.__lshift__)

    def __rshift__(self, other):
        return self._bitwise_op(other=other, handler=operator.__rshift__)
