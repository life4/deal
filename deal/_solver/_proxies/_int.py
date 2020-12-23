import z3
from .._exceptions import UnsupportedError
from ._proxy import ProxySort
from ._registry import registry


@registry.add
class IntSort(ProxySort):
    type_name = 'int'

    @classmethod
    def sort(cls):
        return z3.IntSort()

    @classmethod
    def val(cls, x):
        return z3.IntVal(x)

    @property
    def as_int(self):
        return self

    @property
    def as_float(self):
        # TODO: int to fp?
        return self.as_real

    @property
    def as_real(self):
        cls = registry['float']
        return cls(expr=z3.ToReal(self.expr))

    @property
    def as_fp(self):
        cls = registry['float']
        expr = z3.fpToFP(z3.ToReal(self.expr))
        return cls(expr=expr)

    @property
    def as_str(self):
        cls = registry['str']
        return cls(expr=z3.IntToStr(self.expr))

    def abs(self):
        cls = type(self)
        expr = z3.If(self.expr >= z3.IntVal(0), self.expr, -self.expr)
        return cls(expr=expr)

    def __truediv__(self, other):
        cls = registry['float']
        real = z3.ToReal(self.expr)
        if isinstance(other, IntSort):
            return cls(expr=real / other.as_real.expr)
        if not isinstance(other, cls):
            raise UnsupportedError('unsupported denominator sort', other.sort())
        if other.is_real:
            expr = real / other.as_real.expr
        else:
            expr = self.as_fp / other.as_fp.expr
        return cls(expr=expr)

    def __floordiv__(self, other):
        if isinstance(other, IntSort):
            return IntSort(expr=self.expr / other.expr)
        float_proxy = registry['float']
        if isinstance(other, float_proxy):
            return IntSort(expr=self.expr / other.as_int.expr)
        raise UnsupportedError('unsupported denominator sort', other.sort())
