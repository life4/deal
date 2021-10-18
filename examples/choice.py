import random
from typing import List

import deal


# the list cannot be empty
@deal.pre(lambda items: bool(items))
# result is an element withit the given list
@deal.ensure(lambda items, result: result in items)
@deal.has('random')
def choice(items: List[str]) -> str:
    """Get a random element from the given list.
    """
    return random.choice(items)


test_choice = deal.cases(choice)
