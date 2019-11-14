import deal
import pytest


def test_parameters_and_result_fulfill_constact():
    @deal.ensure(lambda a, b, result: a > 0 and b > 0 and result != 'same number')
    def func(a, b):
        if a == b:
            return 'same number'
        else:
            return 'different numbers'

    assert func(1, 2) == 'different numbers'
    with pytest.raises(deal.PostContractError):
        func(0, 1)
    with pytest.raises(deal.PostContractError):
        func(1, 0)
    with pytest.raises(deal.PostContractError):
        func(1, 1)
