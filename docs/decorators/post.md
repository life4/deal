# post

[Postcondition](https://en.wikipedia.org/wiki/Postcondition) -- condition that must be true after function executed. Raises `PostContractError` otherwise.

```python
@deal.post(lambda x: x > 0)
def always_positive_sum(*args):
    return sum(args)

always_positive_sum(2, -3, 4)
# 3

always_positive_sum(2, -3, -4)
# PostContractError:
```

For async functions it works the same. For generators validation runs for every yielded value:

```python
@deal.post(lambda result: result == 2 or result % 2 == 1)
@deal.post(lambda result: result == 3 or result % 3 != 0)
def get_primary_numbers():
    yield from (2, 3, 5, 7, 11, 13)
```

## Motivation

Post-condition allows to make additional constraints about function result. Use type annotations to limit types of result and post-conditions to limit possible values inside given types. Let's see a few examples.

If function `count` returns count of elements that equal to given element, result is always non-negative.

```python
@deal.post(lambda result: result >= 0)
def count(items: List[str], item: str) -> int:
    ...
```

Or you can make promise that your response always contains some specific fields:

```python
@deal.post(lambda result: 'code' in result)
@deal.post(lambda result: 'records' in result)
def get_usernames(role):
    if role != 'admin':
        return dict(code=403, records=[])
    return dict(code=200, records=['oleg', 'greg', 'admin'])
```
