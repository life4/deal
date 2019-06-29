# pre

[Precondition](https://en.wikipedia.org/wiki/Precondition) -- condition that must be true before function is executed. Raises `PreContractError` otherwise.

```python
@deal.pre(lambda *args: all(arg > 0 for arg in args))
def sum_positive(*args):
    return sum(args)

sum_positive(1, 2, 3, 4)
# 10

sum_positive(1, 2, -3, 4)
# PreContractError:
```
