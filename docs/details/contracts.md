# More about writing contracts

## Simplified signature

The main problem with contracts is that they have to duplicate the original function's signature, including default arguments. While it's not a problem for small examples, things become more complicated when the signature grows. In this case, you can specify a function that accepts only one `_` argument, and deal will pass there a container with arguments of the function call, including default ones:

```python
@deal.pre(lambda _: _.a + _.b > 0)
def f(a, b=1):
    return a + b

f(1)
# 2

f(-2)
# PreContractError: expected a + b > 0 (where a=-2, b=1)
```

## deal.chain

The `deal.chain` decorator allows to merge a few contracts together into one decorator. It can be used to store contracts separately from the function:

```python
contract_for_min = deal.chain(
    deal.pre(lambda items: len(items) > 0),
    deal.ensure(lambda items, result: result in items),
)

@contract_for_min
def min(items):
    ...
```

This allows to reuse contracts among multiple functions. Also,

## Typing

We encourage you to use [type annotations](https://docs.python.org/3/library/typing.html), and so deal is fully type annotated and respects and empowers your type annotations as well. At the same time, deal is very flexible about what can be a validator for a contract (functions, short signatures, Marshmallow schemas etc), and so it cannot be properly described with type annotations. To solve this issue, deal provides a custom plugin for [mypy](http://mypy-lang.org/). **The plugin checks types for validators**. It does not execute contracts.

The best way to configure mypy is using `pyproject.toml`:

```toml
[tool.mypy]
plugins = ["deal.mypy"]
```

Keep in mind that `pyproject.toml` is supported by mypy only starting from version 0.910. Check your installed version by running `mypy --version`. If it is below 0.910, upgrade it by running `python3 -m pip install -U mypy`.
