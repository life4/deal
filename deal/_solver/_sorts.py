import z3


class ListSort:
    @staticmethod
    def make(sort: z3.SortRef) -> z3.SeqRef:
        return z3.Empty(z3.SeqSort(sort))

    @staticmethod
    def append(items: z3.SeqRef, item: z3.ExprRef) -> z3.SeqRef:
        return items + z3.Unit(item)
