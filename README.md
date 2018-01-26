



## Usage

Pre (`pre`, `require`):

```python
In [1]: from contracts import pre, post, inv

In [2]: @pre(lambda *args: all(map(lambda x: x > 0, args)))
   ...: def my_sum(*args):
   ...:     return sum(args)
   ...:

In [3]: my_sum(2, 3, 4)
Out[3]: 9

In [4]: my_sum(2, -3, 4)
PreContractError:
```

Post (`post`, `ensure`):

```python
In [5]: @post(lambda x: x > 0)
   ...: def my_sum(*args):
   ...:     return sum(args)
   ...:

In [6]: my_sum(2, -3, 4)
Out[6]: 3

In [7]: my_sum(2, -3, -4)
PostContractError:
```

Inv (`inv`, `invariant`):

```python
In [8]: @inv(lambda obj: obj.x > 0)
   ...: class A:
   ...:     x = 4
   ...:     

In [9]: a = A()

In [10]: a.x = 10

In [11]: a.x = -10
InvContractError:

In [12]: A
Out[12]: contracts.core.AInvarianted

```

Custom message:

```python
In [13]: @pre(lambda x: x > 0, "x must be > 0")
    ...: def f(x):
    ...:     return x * 2
    ...:

In [14]: f(-2)
PreContractError: x must be > 0
```

Custom exception:

```python
In [15]: @pre(lambda x: x > 0, exception=AssertionError("x must be > 0"))
    ...: def f(x):
    ...:     return x * 2
    ...:

In [16]: f(-2)
AssertionError: x must be > 0
```

Validators (nearly Django Forms style, except initialization):

```python
In [19]: class Validator:
    ...:     def __init__(self, x):
    ...:         self.x = x
    ...:         
    ...:     def is_valid(self):
    ...:         if self.x <= 0:
    ...:             self.errors = ['x must be > 0']
    ...:             return False
    ...:         return True
    ...:     

In [20]: @pre(Validator)
    ...: def f(x):
    ...:     return x * 2
    ...:

In [21]: f(5)
Out[21]: 10

In [22]: f(-5)
PreContractError: ['x must be > 0']
```

Return error message from contract:

```python
In [23]: @pre(lambda x: x > 0 or "x must be > 0")
    ...: def f(x):
    ...:     return x * 2
    ...:

In [24]: f(-5)
PreContractError: x must be > 0
```
