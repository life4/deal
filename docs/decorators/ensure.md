# ensure

Ensure is a [postcondition](./post) that aceepts not only result, but also function arguments. Must be true after function executed. Raises `PostContractError` otherwise.

```python
@deal.ensure(lambda x, result: x != result)
def double(x):
    return x * 2

double(2)
# 4

double(0)
# PostContractError:
```

## Motivation

Perfect for complex task that easy to check. For example:

```python
from typing import List

# element at this position matches item
@deal.ensure(
    lambda items, item, result: items[result] == item,
    message='invalid match',
)
# element at this position is the first match
@deal.ensure(
    lambda items, item, result: not any(el == item for el in items[:result]),
    message='not the first match',
)
def index_of(items: List[int], item: int) -> int:
    for index, element in enumerate(items):
        if element == item:
            return index
    raise LookupError
```

It allows you to simplify testing, easier check hypothesis, tell more about the function behavior.
