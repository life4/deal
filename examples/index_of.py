from typing import List

import deal


# if you have more than 2-3 contracts,
# consider moving them from decorators into separate variable
# like this:
contract_for_index_of = deal.chain(
    # result is an index of items
    deal.post(lambda result: result >= 0),
    deal.ensure(lambda items, item, result: result < len(items)),
    # element at this position matches item
    deal.ensure(
        lambda items, item, result: items[result] == item,
        message='invalid match',
    ),
    # element at this position is the first match
    deal.ensure(
        lambda items, item, result: not any(el == item for el in items[:result]),
        message='not the first match',
    ),
    # LookupError will be raised if no elements found
    deal.raises(LookupError),
    deal.reason(LookupError, lambda items, item: item not in items),
    # no side-effects
    deal.has(),
)


@contract_for_index_of
def index_of(items: List[int], item: int) -> int:
    for index, el in enumerate(items):
        if el == item:
            return index
    raise LookupError


test_index_of = deal.cases(index_of)
