from sys import float_info
import z3
from .._exceptions import UnsupportedError
from ._proxy import ProxySort
from ._registry import registry


@registry.add
class FloatSort(ProxySort):
    type_name = 'float'
    prefer_real = True

    @staticmethod
    def fp_sort():
        return z3.FPSort(ebits=float_info.dig, sbits=float_info.mant_dig)

    @staticmethod
    def real_sort():
        return z3.RealSort()

    @classmethod
    def sort(cls):
        if cls.prefer_real:
            return cls.real_sort()
        return cls.fp_sort()

    @classmethod
    def val(cls, x):
        if cls.prefer_real:
            return z3.RealVal(x)
        return z3.FPVal(x, cls.sort())

    @classmethod
    def _real2fp(cls, x):
        return z3.fpRealToFP(z3.RNE(), x, cls.fp_sort())

    @classmethod
    def _fp2real(cls, x):
        return z3.fpToReal(x)

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
    def as_real(self):
        if self.is_real:
            return self
        cls = type(self)
        return cls(expr=self._fp2real(self.expr))

    @property
    def as_fp(self):
        if self.is_fp:
            return self
        cls = type(self)
        return cls(expr=self._real2fp(self.expr))

    @property
    def as_int(self):
        cls = registry['int']
        return cls(expr=z3.ToInt(self.as_real.expr))

    @property
    def as_str(self):
        raise UnsupportedError('cannot convert float to str')

    def abs(self):
        if self.is_fp:
            return z3.fpAbs(self.expr)
        return z3.If(self.expr >= z3.RealVal(0), self.expr, -self.expr)

    def __truediv__(self, other):
        int_proxy = registry['int']
        if isinstance(other, int_proxy):
            if self.is_real:
                return FloatSort(expr=self.as_real.expr / other.as_real.expr)
            return FloatSort(expr=self.as_fp.expr / other.as_fp.expr)

        if self.is_real and other.is_real:
            return FloatSort(expr=self.expr / other.expr)
        if self.is_fp and other.is_fp:
            return FloatSort(expr=self.expr / other.expr)
        if self.prefer_real:
            return FloatSort(expr=self.expr.as_real / other.as_real.expr)
        return FloatSort(expr=self.expr.as_fp / other.as_fp.expr)

    def __floordiv__(self, other):
        int_proxy = registry['int']
        val = int_proxy(expr=self.as_int.expr / other.as_int.expr)
        return val.as_float
