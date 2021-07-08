from typing import List

import deal


# In short signature, `_` is a `dict` with access by attributes.
# Hence it has all dict attributes. So, if argument we need conflicts
# with a dict attribute, use getitem instead of getattr.
# In the example below, we use `_['items']` instead of `_.items`.

@deal.post(lambda result: result >= 0)
# if count is not zero, `item` appears in `items` at least once.
@deal.ensure(lambda _: _.result == 0 or _['item'] in _['items'])
# if count is zero, `item` is not in `items`
@deal.ensure(lambda _: _.result != 0 or _['item'] not in _['items'])
@deal.has()
def count(items: List[str], item: str) -> int:
    """How many times `item` appears in `items`
    """
    return items.count(item)


test_count = deal.cases(count)
