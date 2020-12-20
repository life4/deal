import z3


def unwrap(obj) -> z3.Z3PPObject:
    if isinstance(obj, CustomSort):
        return obj.expr
    return obj


def wrap(expr):
    if z3.is_seq(expr):
        return ListSort(expr=expr)
    if z3.is_string(expr):
        return StrSort(expr=expr)
    return expr


class CustomSort:
    expr: z3.Z3PPObject


class SeqSort(CustomSort):
    expr: z3.SeqRef

    def __init__(self, expr) -> None:
        self.expr = expr

    @classmethod
    def make_empty(cls, sort: z3.SortRef = None) -> 'SeqSort':
        expr = None
        if sort is not None:
            expr = z3.Empty(z3.SeqSort(sort))
        return cls(expr=expr)

    def append(self, item: z3.ExprRef) -> 'SeqSort':
        cls = type(self)
        unit = z3.Unit(unwrap(item))
        if self.expr is None:
            return cls(expr=unit)
        return cls(expr=self.expr + unit)

    def __bool__(self):
        if self.expr is None:
            return z3.BoolVal(False)
        return z3.Length(self.expr) == z3.IntVal(0)

    def __eq__(self, other: 'SeqSort'):
        return self.expr == unwrap(other)

    def length(self) -> z3.ArithRef:
        if self.expr is None:
            return z3.IntVal(0)
        return z3.Length(self.expr)


class ListSort(SeqSort):
    def contains(self, item):
        unit = z3.Unit(unwrap(item))
        return z3.Contains(self.expr, unit)


class StrSort(SeqSort):
    def __contains__(self, item):
        if isinstance(item, SeqSort):
            item = item.expr
        return z3.Contains(self.expr, item)
