import deal


@deal.reason(ZeroDivisionError, lambda a, b: b == 0)
@deal.reason(ValueError, lambda a, b: a == b, message='a is equal to b')
@deal.raises(ValueError, IndexError, ZeroDivisionError)
@deal.pre(lambda a, b: b != 0)
@deal.pre(lambda a, b: b != 0, message='b is not zero')
@deal.ensure(lambda a, b, result: b != result)
@deal.post(lambda res: res != .13)
@deal.has('database', 'network')
@deal.example(lambda: example(6, 2) == 3)
def example(a: int, b: int) -> float:
    """Example function.

    :return: The description for return value.
    """
    return a / b
