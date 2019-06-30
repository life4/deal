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

## Simple validator

It's almost like Django Forms, except initialization:

```python
class Validator:
    def __init__(self, x):
        self.x = x

    def is_valid(self):
        if self.x <= 0:
            self.errors = ['x must be > 0']
            return False
        return True

@deal.pre(Validator)
def f(x):
    return x * 2

f(5)
# 10

f(-5)
# PreContractError: ['x must be > 0']
```

## Scheme

Scheme is like simple validator, but `data` attribute contains dictionary with all passed arguments:

```python
class NameScheme(Scheme):
    def is_valid(self):
        if not isinstance(self.data['name'], str):
            self.errors = ['name must be str']
            return False
        return True


@deal.pre(NameScheme)
def f(name):
    return name * 2

f('Chris')
# 'ChrisChris'

f(3)
# PreContractError: ['name must be str']
```

Scheme automatically detect all arguments names:

```python
class Printer(Scheme):
    def is_valid(self):
        print(self.data)
        return True


@deal.pre(Printer)
def f(a, b, c=4, *args, **kwargs):
    pass

f(1, b=2, e=6)
{'args': (), 'a': 1, 'b': 2, 'c': 4, 'e': 6, 'kwargs': {'e': 6}}

f(1, 2, 3, 4, 5, 6)
{'a': 1, 'b': 2, 'c': 3, 'args': (4, 5, 6), 'kwargs': {}}
```

## Marshmallow, WTForms, PyScheme etc.

You can use any validators from [djburger](https://github.com/orsinium/djburger). See [validators documentation](https://djburger.readthedocs.io/en/latest/validators.html) and [list of supported external libraries](https://github.com/orsinium/djburger#external-libraries-support). For example, deal + djburger + [marshmallow](https://marshmallow.readthedocs.io/en/latest/):

```python
import djburger, marshmallow

class Scheme(djburger.v.b.Marshmallow):
    name = marshmallow.fields.Str()

@deal.pre(Scheme)
def func(name):
    return name * 2

func('Chris')
'ChrisChris'

func(123)
# PreContractError: {'name': ['Not a valid string.']}
```

Djburger is Django independent. You can use it in any python projects.
