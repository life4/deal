# Deal

**Deal** -- python library for [design by contract](https://en.wikipedia.org/wiki/Design_by_contract) (DbC) programming.

This library contain 3 main conception from DbC:

* [Precondition](https://en.wikipedia.org/wiki/Precondition) -- condition that must always be true just prior to the execution of function.
* [Postcondition](https://en.wikipedia.org/wiki/Postcondition) -- condition that must always be true just after the execution of function.
* [Invariant](https://en.wikipedia.org/wiki/Invariant) -- condition that can be relied upon to be true during execution of a program. In this library invariant condition check in 3 cases:
    1. Before class method execution.
    2. After class method execution.
    3. After some class attribute setting.


## Features

* Functional declaration for conditions.
* Custom exceptions for best usage in try-except block.
* Ability to set optional error message and (or) exception class.
* Ability to return error message from contact.
* Ability to use Django Form styled validators as contracts.
* Attribute setting validation by invariant.
* Validation by invariant dinamically setted attributes and methods.
* Readable source code (all decorators implemented by classes)


## Installation

Stable:

```bash
pip install deal
```

Dev:

```bash
pip install -e git+https://github.com/orsinium/deal.git#egg=deal
```

## TL;DR

* `@pre` -- validate function arguments (pre-validation).
* `@post` -- validate function result (post-validation).
* `@inv` -- validate class methods before and after some method calling and after attribute setting.


## Exceptions structure:

* ContractError (inherited from built-in AssertionError)
    * PreContractError
    * PostContractError
    * InvContractError

Library decorators doesn't catch any exceptions raised from contracts.


## Usage

Pre (`pre`, `require`):

```python
In [1]: from deal import pre, post, inv, ContractError

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
