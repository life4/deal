# Validators

## Simplified signature

The main problem with contracts is that they have to duplicate the original function's signature, including default arguments. While it's not a problem for small examples, things become more complicated when the signature grows. For this case, you can specify a function that accepts only one `_` argument, and deal will pass here a container with arguments of the function call, including default ones:

```python
@deal.pre(lambda _: _.a + _.b > 0)
def f(a, b=1):
    return a + b

f(1)
# 2

f(-2)
# PreContractError:
```

## Providing an error

Regular contract can return error message instead of `False`:

```python
def contract(name):
    if not isinstance(name, str):
        return 'name must be str'
    return True

@deal.pre(contract)
def f(x):
    return x * 2

f('Chris')
# 'ChrisChris'

f(4)
# PreContractError: name must be str
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
# PreContractError: {'name': ['Not a valid string.']}
```

See [vaa](https://github.com/life4/vaa) documentation for details.
