from typing import List, TypeVar

import deal
import pytest


T = TypeVar('T')


@deal.pre(lambda items: len(items) > 0)
@deal.has()
def my_min(items: List[T]) -> T:
    return min(items)


@deal.has('stdout')
def example():
    # good
    print(my_min([3, 1, 4]))
    # bad
    print(my_min([]))


@pytest.mark.parametrize('case', deal.cases(my_min))
def test_min(case):
    case()
