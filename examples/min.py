from typing import List, TypeVar

import deal
import pytest


T = TypeVar('T')


@deal.pre(lambda items: len(items) > 0)
@deal.has()
def my_min(items: List[T]) -> T:
    return min(items)


@deal.has()
def example():
    # good
    my_min([3, 1, 4])
    # bad
    my_min([])
    return 0


@pytest.mark.parametrize('case', deal.cases(my_min))
def test_min(case):
    case()
