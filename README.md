# Deal

![Deal Logo](logo.png)

[![Build Status](https://travis-ci.org/orsinium/deal.svg?branch=master)](https://travis-ci.org/orsinium/deal) [![PyPI version](https://img.shields.io/pypi/v/deal.svg)](https://pypi.python.org/pypi/deal) [![Status](https://img.shields.io/pypi/status/deal.svg)](https://pypi.python.org/pypi/deal) [![Code size](https://img.shields.io/github/languages/code-size/orsinium/deal.svg)](https://github.com/orsinium/deal) [![License](https://img.shields.io/pypi/l/deal.svg)](LICENSE)

**Deal** -- python library for [design by contract](https://en.wikipedia.org/wiki/Design_by_contract) (DbC) programming.

This library contain 3 main conception from DbC:

* [Precondition](https://en.wikipedia.org/wiki/Precondition) -- condition that must be true before function is executed.
* [Postcondition](https://en.wikipedia.org/wiki/Postcondition) -- condition that must be true after function executed.
* [Invariant](https://en.wikipedia.org/wiki/Invariant) -- condition that can be relied upon to be true during execution of a program. In this library invariant condition check in 3 cases:
    1. Before class method execution.
    2. After class method execution.
    3. After some class attribute setting.


## Features

* Functional declaration.
* Custom exceptions.
* Raising exceptions from contract.
* Django Forms styled validators.
* Attribute setting invariant validation.
* Dynamically assigned attributes and methods invariant validation.


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
Out[12]: deal.core.AInvarianted

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
In [17]: class Validator:
    ...:     def __init__(self, x):
    ...:         self.x = x
    ...:         
    ...:     def is_valid(self):
    ...:         if self.x <= 0:
    ...:             self.errors = ['x must be > 0']
    ...:             return False
    ...:         return True
    ...:     

In [18]: @pre(Validator)
    ...: def f(x):
    ...:     return x * 2
    ...:

In [19]: f(5)
Out[19]: 10

In [20]: f(-5)
PreContractError: ['x must be > 0']
```

Return error message from contract:

```python
In [21]: @pre(lambda x: x > 0 or "x must be > 0")
    ...: def f(x):
    ...:     return x * 2
    ...:

In [22]: f(-5)
PreContractError: x must be > 0
```

Contracts chaining:

```python
In [23]: @pre(lambda x: x > 0)
   ...: @pre(lambda x: x < 10)
   ...: def f(x):
   ...:     return x * 2
   ...:

In [24]: f(5)
Out[24]: 10

In [25]: f(-1)
PreContractError:

In [26]: f(12)
PreContractError:
```


## Contracts chaining order

* `@inv`: from top to bottom.
* `@pre`: from top to bottom.
* `@post`: from bottom to top.


## Perfomance

**NOTICE**: `1 µs == 1000 ns`

`@pre` and `@post`:

```python
In [27]: f = lambda x: x

In [28]: pre_f = pre(lambda x: True)(f)

In [29]: post_f = post(lambda x: True)(f)

In [30]: %timeit f(10)
92.3 ns ± 3.62 ns per loop (mean ± std. dev. of 7 runs, 10000000 loops each)

In [31]: %timeit pre_f(10)
2.07 µs ± 92.5 ns per loop (mean ± std. dev. of 7 runs, 100000 loops each)

In [32]: %timeit post_f(10)
2.03 µs ± 18.6 ns per loop (mean ± std. dev. of 7 runs, 100000 loops each)
```

+1 µs

`@inv`:

```python
In [33]: class A:
    ...:     x = 4
    ...:     

In [34]: InvA = inv(lambda obj: True)(A)

In [35]: a = A()

In [36]: inv_a = InvA()

In [37]: %timeit a.x = 10
76.4 ns ± 1.36 ns per loop (mean ± std. dev. of 7 runs, 10000000 loops each)

In [38]: %timeit inv_a.x = 10
6.89 µs ± 408 ns per loop (mean ± std. dev. of 7 runs, 100000 loops each)
```

+6 µs


## TODO

* Django Forms native support
* Marshmallow native support

