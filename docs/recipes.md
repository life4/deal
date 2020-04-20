# Recipes

Some ideas that are useful in the real world applications.

## Keep contracts simple

If a function accepts only a few short arguments, duplicate the original signature (without annotations) for contracts:

```python
@deal.pre(lambda left, right: right != 0)
def div(left: float, right: float) -> float:
    return left / right
```

Otherwise, or if a function has default arguments, use simplified signature for contracts:

```python
@deal.pre(lambda _: _.default is not None or _.right != 0)
def div(left: float, right: float, default: float = None) -> float:
    try:
        return left / right
    except ZeroDivisionError:
        if default is not None:
            return default
        raise
```

## Type checks

Never check types with deal. [Mypy](https://github.com/python/mypy) does it much better. Also, there are [plenty of alternatives](https://github.com/typeddjango/awesome-python-typing) for both static and dynamic validation. Deal is intended to empower types, say a bit more about possible values set than you can do with type annotations, not replace them. However, if you want to play with deal a bit or make types a part of contracts, [PySchemes](https://github.com/spy16/pyschemes)-based contract is the best choice:

```python
import deal
from pyschemes import Scheme

@deal.pre(Scheme(dict(left=str, right=str)))
def concat(left, right):
    return left + right

concat('ab', 'cd')
# 'abcd'

concat(1, 2)
# PreContractError: at key 'left' (expected type: 'str', got 'int')
```

## Prefer `pre` and `post` over `ensure`

If a contract needs only function arguments, use `pre`. If a contract checks only function result, use `post`. And only if a contract need both input and output values at the same time, use `ensure`. Keeping available namespace for contract as small as possible makes the contract signature simpler and helps with partial execution in the linter.

## Prefer `reason` over `raises`

Always try your best to tell why exception can be raised.

## Keep module initialization pure

Nothing should happen on module load. Create some constants, compile regexpes, and that's all. Make it lazy.

```python
deal.module_load(deal.pure)
```

## Contract shouldn't be important

Never catch contract errors. Never rely on them in runtime. They are for tests and humans. The shouldn't have an actual logic, only validate it.
