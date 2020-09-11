# Validators

In most of the cases, contracts are small and simple. However, sometimes you want to have a complex contract or reuse an existing validator for it. In this case, this section is for you.

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
