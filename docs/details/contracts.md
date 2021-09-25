# More on writing contracts

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

The {py:func}`deal.chain` decorator allows to merge a few contracts together into one decorator. It can be used to store contracts separately from the function:

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

## Providing an error

You can provide `message` argument for a contract, and this message will be used as the error message (and in [documentation](./docs)):

```python
@deal.pre(lambda x: x > 0, message='x must be positive')
def f(x):
    return list(range(x))

f(-2)
# PreContractError: x must be positive (where x=-2)
```

If a single contract includes multiple checks, it can return an error message instead of `False`, so different failures can be distinguished:

```python
def contract(x):
    if not isinstance(x, int):
        return 'x must be int'
    if x <= 0:
        return 'x must be positive'
    return True

@deal.pre(contract)
def f(x):
    return list(range(x))

f('Aragorn')
# PreContractError: x must be int (where x='Aragorn')

f(-2)
# PreContractError: x must be positive (where x=-2)
```

## External validators

Deal supports a lot of external validation libraries, like Marshmallow, WTForms, PyScheme etc. For example:

```python
import deal
import marshmallow

class Schema(marshmallow.Schema):
    name = marshmallow.fields.Str()

@deal.pre(Schema)
def func(name):
    return name * 2

func('Chris')
'ChrisChris'

func(123)
# PreContractError: [Error(message='Not a valid string.', field='name')] (where name=123)
```

See [vaa](https://github.com/life4/vaa) documentation for details.
