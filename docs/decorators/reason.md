# reason

Checks condition if exception was raised.

```python
@deal.reason(ZeroDivisionError, lambda a, b: b == 0)
def divide(a, b):
    return a / b
```

## Motivation

This is the [@deal.ensure](ensure) for exceptions. It works perfect when it's easy to check correctness of conditions when exception is raised.

For example, if function `index_of` returns index of the first element that equal to the given element and raises `LookupError` if element is not found, we can check that if `LookupError` is raised, element not in the list:

```python
@deal.reason(LookupError, lambda items, item: item not in items)
def index_of(items: List[int], item: int) -> int:
    for index, el in enumerate(items):
        if el == item:
            return index
    raise LookupError
```
