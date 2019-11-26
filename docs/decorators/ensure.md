# ensure

Ensure is a [postcondition](./post) that accepts not only result, but also function arguments. Must be true after function executed. Raises `PostContractError` otherwise.

```python
@deal.ensure(lambda x, result: x != result)
def double(x):
    return x * 2

double(2)
# 4

double(0)
# PostContractError:
```

For async functions it works the same. For generators validation runs for every yielded value:

```python
@deal.ensure(lambda start, end, result: start <= result < end)
def range(start, end):
    step = start
    while step < end:
        yield step
        step += 1
```

## Motivation

Ensure allows you to simplify testing, easier check hypothesis, tell more about the function behavior. It works perfect for [P vs NP](https://en.wikipedia.org/wiki/P_versus_NP_problem) like problems. In other words, for complex task when checking result correctness (even partial checking only for some cases) is much easier then calculation itself. For example:

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

Also, it's ok if you can check only some simple cases. For example, function `map` applies given function to the list. Let's check that count of returned elements is the same as the count of given elements:

```python
from typing import Callable, List

@deal.ensure(lambda: items, func, result: len(result) == len(items))
def map(items: List[str], func: Callable[[str], str]) -> List[str]:
    ...
```

Or if function `choice` returns random element from the list, we can't from one run check result randomness, but can't ensure that result is an element from the list:

```python
@deal.ensure(lambda items, result: result in items)
def choice(items: List[str]) -> str:
    ...
```
