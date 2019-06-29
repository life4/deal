# Validators

1. Regular contract with errors returning:

```python
In [1]: def contract(name):
   ...:     if not isinstance(name, str):
   ...:         return "name must be str"
   ...:     return True
   ...:

In [2]: @pre(contract)
   ...: def f(x):
   ...:     return x * 2
   ...:

In [3]: f('Chris')
Out[3]: 'ChrisChris'

In [4]: f(4)
PreContractError: name must be str
```

2. Simple validator (nearly Django Forms style, except initialization):

```python
In [1]: class Validator:
   ...:     def __init__(self, x):
   ...:         self.x = x
   ...:         
   ...:     def is_valid(self):
   ...:         if self.x <= 0:
   ...:             self.errors = ['x must be > 0']
   ...:             return False
   ...:         return True
   ...:     

In [2]: @pre(Validator)
   ...: def f(x):
   ...:     return x * 2
   ...:

In [3]: f(5)
Out[3]: 10

In [4]: f(-5)
PreContractError: ['x must be > 0']
```

3. Scheme like simple validator but `data` attribute contains dictionary with all passed arguments:

```python

In [1]: class NameScheme(Scheme):
   ...:     def is_valid(self):
   ...:         if not isinstance(self.data['name'], str):
   ...:             self.errors = ['name must be str']
   ...:             return False
   ...:         return True
   ...:     

In [2]: @pre(NameScheme)
   ...: def f(name):
   ...:     return name * 2
   ...:

In [3]: f('Chris')
Out[3]: 'ChrisChris'

In [4]: f(3)
PreContractError: ['name must be str']
```

Scheme automatically detect all arguments names:

```python
In [1]: class Printer(Scheme):
   ...:     def is_valid(self):
   ...:         print(self.data)
   ...:         return True
   ...:     

In [2]: @pre(Printer)
   ...: def f(a, b, c=4, *args, **kwargs):
   ...:     pass
   ...:

In [3]: f(1, b=2, e=6)
{'args': (), 'a': 1, 'b': 2, 'c': 4, 'e': 6, 'kwargs': {'e': 6}}

In [4]: f(1, 2, 3, 4, 5, 6)
{'a': 1, 'b': 2, 'c': 3, 'args': (4, 5, 6), 'kwargs': {}}
```

4. You can use any validators from [djburger](https://github.com/orsinium/djburger). See [validators documentation](https://djburger.readthedocs.io/en/latest/validators.html) and [list of supported external libraries](https://github.com/orsinium/djburger#external-libraries-support). For example, deal + djburger + [marshmallow](https://marshmallow.readthedocs.io/en/latest/):

```python
In [1]: import djburger, marshmallow

In [2]: class Scheme(djburger.v.b.Marshmallow):
   ...:     name = marshmallow.fields.Str()
   ...:

In [3]: @pre(Scheme)
   ...: def func(name):
   ...:     return name * 2
   ...:

In [4]: func('Chris')
Out[4]: 'ChrisChris'

In [5]: func(123)
PreContractError: {'name': ['Not a valid string.']}
```

Djburger is Django independent. You can use it in any python projects.
