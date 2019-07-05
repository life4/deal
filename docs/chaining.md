# Contracts chaining

You can chain any contracts:

```python
@deal.pre(lambda x: x > 0)
@deal.pre(lambda x: x < 10)
def f(x):
    return x * 2

f(5)
# 10

f(-1)
# PreContractError:

f(12)
# PreContractError:
```

`@deal.post` contracts are chaining from bottom to top. All other contracts are chaining from top to bottom.
