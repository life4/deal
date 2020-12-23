from sys import float_info
import typing
import astroid
import z3
from ._exceptions import UnsupportedError
from ._context import Context


def unwrap(obj) -> z3.Z3PPObject:
    if not isinstance(obj, ProxySort):
        return obj
    expr = obj.expr
    if expr is None:
        return obj.make_empty_expr(z3.IntSort())
    return expr


def wrap(expr):
    if isinstance(expr, ProxySort):
        return expr
    if z3.is_string(expr):
        return StrSort(expr=expr)
    if z3.is_seq(expr):
        return ListSort(expr=expr)
    if z3.is_array(expr):
        return SetSort(expr=expr)
    if z3.is_fp(expr):
        return FloatSort(expr=expr)
    if z3.is_real(expr):
        return FloatSort(expr=expr)
    if z3.is_int(expr):
        return IntSort(expr=expr)
    return expr


def if_expr(test, val_then, val_else):
    return wrap(z3.If(test, unwrap(val_then), unwrap(val_else)))


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


class IntSort(ProxySort):
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
        return FloatSort(expr=z3.ToReal(self.expr))

    @property
    def as_fp(self):
        expr = z3.fpToFP(z3.ToReal(self.expr))
        return FloatSort(expr=expr)

    @property
    def as_str(self):
        return StrSort(expr=z3.IntToStr(self.expr))

    def abs(self):
        cls = type(self)
        expr = z3.If(self.expr >= z3.IntVal(0), self.expr, -self.expr)
        return cls(expr=expr)

    def __truediv__(self, other):
        real = z3.ToReal(self.expr)
        if isinstance(other, IntSort):
            return FloatSort(expr=real / other.as_real.expr)
        if not isinstance(other, FloatSort):
            raise UnsupportedError('unsupported denominator sort', other.sort())
        if other.is_real:
            expr = real / other.as_real.expr
        else:
            expr = self.as_fp / other.as_fp.expr
        return FloatSort(expr=expr)

    def __floordiv__(self, other):
        if isinstance(other, IntSort):
            return IntSort(expr=self.expr / other.expr)
        if isinstance(other, FloatSort):
            return IntSort(expr=self.expr / other.as_int.expr)
        raise UnsupportedError('unsupported denominator sort', other.sort())


class FloatSort(ProxySort):
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
        return IntSort(expr=z3.ToInt(self.as_real.expr))

    @property
    def as_str(self):
        raise UnsupportedError('cannot convert float to str')

    def abs(self):
        if self.is_fp:
            return z3.fpAbs(self.expr)
        return z3.If(self.expr >= z3.RealVal(0), self.expr, -self.expr)

    def __truediv__(self, other):
        if isinstance(other, IntSort):
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
        val = IntSort(expr=self.as_int.expr / other.as_int.expr)
        return val.as_float


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

    def length(self) -> z3.ArithRef:
        if self.expr is None:
            return z3.IntVal(0)
        return z3.Length(self.expr)

    def __bool__(self):
        if self.expr is None:
            return z3.BoolVal(False)
        return z3.Length(self.expr) == z3.IntVal(0)


class ListSort(SeqSort):
    def append(self, item: z3.ExprRef) -> 'SeqSort':
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
        return z3.IndexOf(self.expr, unit, start)


class StrSort(SeqSort):
    @staticmethod
    def make_empty_expr(sort=None):
        return z3.Empty(z3.StringSort())

    def _ensure(self, item, seq=False):
        pass

    @classmethod
    def make_empty(cls, sort: z3.SortRef = None) -> 'StrSort':
        expr = cls.make_empty_expr(sort)
        return cls(expr=expr)

    @classmethod
    def convert(cls, obj):
        if z3.is_int(obj):
            return cls(expr=z3.IntToStr(obj))
        raise UnsupportedError('cannot convert', obj, 'to str')

    @property
    def as_int(self):
        return IntSort(expr=z3.StrToInt(self.expr))

    @property
    def as_str(self):
        return self

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


class LambdaSort(typing.NamedTuple):
    ctx: Context
    args: astroid.Arguments
    body: astroid.Expr

    def __call__(self, *values, **kwargs):
        from ._eval_expr import eval_expr

        body_ctx = self.ctx.make_child()
        for arg, value in zip(self.args.arguments, values):
            body_ctx.scope.set(name=arg.name, value=value)
        return eval_expr(node=self.body, ctx=body_ctx)
