# More on writing contracts

## Generating contracts

The best way to get started with deal is to automatically generate some contracts using {ref}`details/cli:decorate` CLI command:

```bash
python3 -m deal decorate my_project/
```

It will run {doc}`/basic/linter` on your code and add some of the missed contracts. The rest of the contracts are still on you, though. Also, you should carefully check the generated code for correctness, because deal may miss something.

The following contracts are supported by the command and will be added to your code:

+ {py:func}`deal.has`
+ {py:func}`deal.raises`
+ {py:func}`deal.safe`

## Simplified signature

The main problem with contracts is that they have to duplicate the original function's signature, including default arguments. While it's not a problem for small examples, things become more complicated when the signature grows. In this case, you can specify a function that accepts only one `_` argument, and deal will pass a container with arguments of the function call to it, including default ones:

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

The {py:func}`deal.chain` decorator allows you to merge a few contracts together into one decorator. It can be used to store contracts separately from the function:

```python run
contract_for_min = deal.chain(
    deal.pre(lambda items: len(items) > 0),
    deal.ensure(lambda items, result: result in items),
)

@contract_for_min
def min(items):
    ...
```

This allows you to reuse contracts among multiple functions. Also, it keeps the function signature cleaner, as multiple decorators may make it a bit noisy.

## deal.inherit

The {py:func}`deal.chain` decorator makes a method to inherit contracts from the base class.

It can be applied to a separate method:

```python
class Shape:
    @deal.post(lambda r: r > 0)
    def get_sides(self):
        raise NotImplementedError

class Triangle(Shape):
    @deal.inherit
    def get_sides(self):
        return 3

triangle = Triangle()
triangle.get_sides()
```

Or to the whole class, so all contracts for all methods will be inherited:

```python
@deal.inherit
class Line(Shape):
    def get_sides(self):
        return 2

line = Line()
line.get_sides()
# PreContractError: expected r > 0 (where r=2)
```

If the class has multiple base classes, contracts from all of them will be inherited.

If the method already has other contracts or decorators, they will be preserved. Just make sure they all are specified below `@deal.inherit`.

## Typing

We encourage you to use [type annotations](https://docs.python.org/3/library/typing.html), and so deal is fully type annotated and respects and empowers your type annotations as well. At the same time, deal is very flexible about what can be a validator for a contract (functions, short signatures, Marshmallow schemas etc), and so it cannot be properly described with type annotations. To solve this issue, deal provides a custom plugin for [mypy](http://mypy-lang.org/). **The plugin checks types for validators**. It does not execute contracts.

The best way to configure mypy is using `pyproject.toml`:

```toml
[tool.mypy]
plugins = ["deal.mypy"]
```

Keep in mind that `pyproject.toml` is supported by mypy only starting from version 0.910. Check your installed version by running `mypy --version`. If it is below 0.910, upgrade it by running `python3 -m pip install -U mypy`.

## Providing an error

You can provide the `message` argument for a contract, and this message will be used as the error message (and in [documentation](./docs)):

```python
@deal.pre(lambda x: x > 0, message='x must be positive')
def f(x):
    return list(range(x))

f(-2)
# PreContractError: x must be positive (where x=-2)
```

If a single contract includes multiple checks, it can return an error message instead of `False`, so that different failures can be distinguished:

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

## Performance

Deal tries to be as performant as possible, with the following goals in mind:

+ If something can be done only once (in other words, cached) with a benefit to performance, it must be done only once.
+ Heavy operations must not be performed when decorator is just applied. Otherwise, it negatively affects the import time for the project that uses deal.
+ Simplicity must not be sacrificed for performance.

The outcome of this is that deal has some heavy operations. Namely, introspection of the wrapped function and the validator. These operations are performed only once, when the function is called for the first time. The idea is similar to how Just-In-Time compilation works in [Julia](https://julialang.org/): compile it only when you need it.

So, if you benchmark a function decorated with deal, you can either:

+ Disable contracts using {py:func}`deal.disable`;
+ Call the function once in advance to trigger the caching;
+ Or pre-cache contracts for a specific function using {py:func}`deal.introspection.init_all`.
