# external
import pytest

# project
import deal


@deal.raises(ZeroDivisionError)
@deal.reason(ZeroDivisionError, lambda _: _.right == 0)
@deal.has()
def div1(left: float, right: float) -> float:
    """
    This implementation allows zero to be passed
    but raises ZeroDivisionError in that case.
    """
    return left / right


@deal.pre(lambda _: _.right != 0)
@deal.has()
def div2(left: float, right: float) -> float:
    """
    This implementation doesn't allow zero to be passed in a function.
    If it is accidentally passed, PreConditionError will be raised
    and the funcrion won't be executed.
    """
    return left / right


# TESTS


@pytest.mark.parametrize('case', deal.cases(div1))
def test_div1(case):
    case()


@pytest.mark.parametrize('case', deal.cases(div2))
def test_div2(case):
    case()
