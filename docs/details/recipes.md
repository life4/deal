# Recipes

Some ideas that are useful in the real world applications.

## Keep contracts simple

If a function accepts only a few short arguments, duplicate the original signature (without annotations) for contracts:

```python run
@deal.pre(lambda left, right: right != 0)
def div(left: float, right: float) -> float:
    return left / right
```

Otherwise, or if a function has default arguments, use simplified signature for contracts:

```python run
@deal.pre(lambda _: _.default is not None or _.right != 0)
def div(left: float, right: float, default: float = None) -> float:
    try:
        return left / right
    except ZeroDivisionError:
        if default is not None:
            return default
        raise
```

## Don't check types

Never check types with deal. [MyPy](https://github.com/python/mypy) does it much better. Also, there are [plenty of alternatives](https://github.com/typeddjango/awesome-python-typing) for both static and dynamic validation. Deal is intended to empower types, to tell a bit more about possible values set than you can do with type annotations, not replace them. However, if you want to play with deal a bit or make types a part of contracts, [PySchemes](https://github.com/spy16/pyschemes)-based contract is a good solution:

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

Always try your best to tell why exception can be raised. However, keep in mind that all exceptions from `reason` still have to be explicitly specified in `raises` since contracts are isolated and have no way to exchange information between each other:

```python run
@deal.reason(ZeroDivisionError, lambda a, b: b == 0)
@deal.raises(ZeroDivisionError)
def divide(a, b):
    return a / b
```

## Keep module initialization pure

Nothing should happen on module load. Create some constants, compile RegExes, and that's all. Make it lazy.

```python
deal.module_load(deal.pure)
```

## Contracts shouldn't be important

Never catch contract errors. Never rely on them in runtime. They are for tests and humans. The shouldn't have an actual logic, only validate it.

## Short signature conflicts

In short signature, `_` is a `dict` with access by attributes. Hence it has all dict attributes. So, if argument we need conflicts with a dict attribute, use getitem instead of getattr. For example, we should use `_['items']` instead of `_.items`.

## Keep contracts pure

You can use any logic inside the validator. However, thumb up rule is to keep contracts [pure](https://en.wikipedia.org/wiki/Pure_function) (without any side-effects, even logging). The main motivation for it is that some contracts can be partially executed by [linter](../basic/linter.md).

## The `message` is a description, not an error

The `message` argument should tell what is expected behavior without assuming that the user violated it. This is because the users can encounter it not only when a `ContractError` is raised but also when they just read the source code or [generated documentation](./docs). For example, if your contract checks that `b >= 0`, don't say "b is negative" (what is violated), say "b must be non-negative" (what is expected).

## Markers are not only side-effects

The `@deal.has` decorator is used to track markers. Some of the markers describing side-effects (like `stdout`) are predefined and detected by linter and in runtime. However, markers can be also used to track anything else you'd like to track in your code. A few examples:

+ Functions that are usually slow.
+ Functions that can be called only for a user with admin access.
+ Functions that access the database.
+ Functions that access the patient data.
+ Functions that can only work with some additional dependencies installed.
+ Deprecated functions.
+ Functions that need refactoring.

## Permissive license

Deal is distributed under [MIT License](https://en.wikipedia.org/wiki/MIT_License) which is a permissive license with high [license compatibility](https://en.wikipedia.org/wiki/License_compatibility). However, Deal has [astroid](https://github.com/PyCQA/astroid) in the dependencies which is licensed under [LGPL](https://en.wikipedia.org/wiki/GNU_Lesser_General_Public_License). While this license allows to be used in non-LGPL proprietary software too, it still can be not enough for some companies. So, if the legal department in your company forbids using LGPL libraries in transitive dependencies, you can freely remove `astroid` from the project dependencies before shipping it on the production. All CLI commands won't work anymore but runtime checks will.
