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
