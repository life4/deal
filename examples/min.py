from typing import List

import deal


@deal.pre(lambda items: len(items) > 0)
@deal.has()
def my_min(items: List[int]) -> int:
    return min(items)


@deal.has('stdout')
def example():
    # good
    print(my_min([3, 1, 4]))
    # bad
    print(my_min([]))


test_min = deal.cases(my_min)
