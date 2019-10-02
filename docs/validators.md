# Validators

## Simple contract

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

For a complex validation you can wrap your contract into [vaa](https://github.com/life4/vaa). It supports Marshmallow, WTForms, PyScheme etc. For example:

```python
import deal
import marshmallow
import vaa

@vaa.marshmallow
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
