from sys import float_info
import z3
from .._exceptions import UnsupportedError
from ._proxy import ProxySort
from ._registry import registry


@registry.add
class FloatSort(ProxySort):
    type_name = 'float'
    prefer_real = False

    def __new__(cls, expr=None):
        if cls is not FloatSort or expr is None:
            return super().__new__(cls)
        if z3.is_real(expr):
            return RealSort.__new__(RealSort)
        return FPSort.__new__(FPSort)

    def __init__(self, expr) -> None:
        self.expr = expr

    @classmethod
    def sort(cls):
        if cls.prefer_real:
            return RealSort.sort()
        return FPSort.sort()

    @classmethod
    def val(cls, x, ctx: z3.Context = None):
        if cls.prefer_real:
            return RealSort.val(x, ctx=ctx)
        return FPSort.val(x, ctx=ctx)

    @classmethod
    def wrap(cls, expr):
        if z3.is_real(expr):
            return RealSort(expr=expr)
        if z3.is_fp(expr):
            return FPSort(expr=expr)
        raise RuntimeError('unreachable')

    @staticmethod
    def fp_sort():
        return FPSort.sort()

    @staticmethod
    def real_sort():
        return z3.RealSort()

    @property
    def as_float(self):
        return self

    @property
    def is_real(self) -> bool:
        return z3.is_real(self.expr)

    @property
    def is_fp(self) -> bool:
        return z3.is_fp(self.expr)

    @property
    def as_str(self):
        raise UnsupportedError('cannot convert float to str')

    def __floordiv__(self, other):
        int_proxy = registry['int']
        val = int_proxy(expr=self.as_int.expr / other.as_int.expr)
        return val.as_float


class RealSort(FloatSort):
    @classmethod
    def sort(cls):
        return z3.RealSort()

    @classmethod
    def val(cls, x, ctx: z3.Context = None):
        return RealSort(expr=z3.RealVal(x, ctx=ctx))

    @classmethod
    def _as_fp(cls, x):
        return z3.fpRealToFP(z3.RNE(), x, cls.fp_sort())

    @property
    def as_float(self):
        return self

    @property
    def as_real(self):
        return self

    @property
    def as_fp(self):
        return FPSort(expr=self._as_fp(self.expr))

    @property
    def as_int(self):
        cls = registry['int']
        return cls(expr=z3.ToInt(self.expr))

    @property
    def as_bool(self):
        return self.expr == z3.RealVal(0)

    @property
    def abs(self):
        expr = z3.If(self.expr >= z3.RealVal(0), self.expr, -self.expr)
        return RealSort(expr=expr)

    @property
    def is_nan(self):
        return z3.BoolVal(False)

    def _binary_op(self, other, handler):
        int_proxy = registry['int']
        if isinstance(other, int_proxy):
            return handler(self.expr, other.as_real.expr)
        if not isinstance(other, FloatSort):
            raise UnsupportedError('cannot combine float and', type(other))
        if other.is_real:
            return handler(self.expr, other.expr)
        if self.prefer_real:
            return handler(self.expr, other.as_real.expr)
        return handler(self.as_fp.expr, other.expr)

    def __truediv__(self, other):
        int_proxy = registry['int']
        if isinstance(other, int_proxy):
            return RealSort(expr=self.as_real.expr / other.as_real.expr)

        if other.is_real:
            return RealSort(expr=self.expr / other.expr)
        if self.prefer_real:
            return RealSort(expr=self.expr / other.as_real.expr)
        return FPSort(expr=self.expr.as_fp / other.as_fp.expr)


class FPSort(FloatSort):

    @staticmethod
    def sort():
        # return z3.Float32()
        return z3.FPSort(ebits=float_info.dig, sbits=float_info.mant_dig)

    @classmethod
    def val(cls, x, ctx: z3.Context = None):
        return FPSort(expr=z3.FPVal(x, cls.sort(), ctx=ctx))

    @classmethod
    def _as_real(cls, x):
        return z3.fpToReal(x)

    @property
    def as_float(self):
        return self

    @property
    def as_real(self):
        return RealSort(expr=self._as_real(self.expr))

    @property
    def as_fp(self):
        return self

    @property
    def as_int(self):
        cls = registry['int']
        return cls(expr=z3.ToInt(self.as_real.expr))

    @property
    def as_bool(self):
        return self.expr == z3.FPVal(0, self.fp_sort())

    @property
    def is_nan(self):
        return z3.fpIsNaN(self.expr)

    @property
    def abs(self):
        return FPSort(expr=z3.fpAbs(self.expr))

    def _binary_op(self, other, handler):
        int_proxy = registry['int']
        if isinstance(other, int_proxy):
            return handler(self.expr, other.as_fp.expr)
        if not isinstance(other, FloatSort):
            raise UnsupportedError('cannot combine float and', type(other))
        if other.is_fp:
            return handler(self.expr, other.expr)
        if self.prefer_real:
            return handler(self.as_real.expr, other.expr)
        return handler(self.expr, other.as_fp.expr)

    def __truediv__(self, other):
        int_proxy = registry['int']
        if isinstance(other, int_proxy):
            return FPSort(expr=self.as_fp.expr / other.as_fp.expr)

        if other.is_fp:
            return FPSort(expr=self.expr / other.expr)
        if self.prefer_real:
            return RealSort(expr=self.as_real.expr / other.as_real.expr)
        return FPSort(expr=self.expr / other.as_fp.expr)

    def __eq__(self, other):
        return self._comp_op(other=other, handler=z3.fpEQ)

    def __ne__(self, other):
        return self._comp_op(other=other, handler=z3.fpNEQ)

    def __gt__(self, other):
        return self._comp_op(other=other, handler=z3.fpGT)

    def __ge__(self, other):
        return self._comp_op(other=other, handler=z3.fpGEQ)

    def __lt__(self, other):
        return self._comp_op(other=other, handler=z3.fpLT)

    def __le__(self, other):
        return self._comp_op(other=other, handler=z3.fpLEQ)
