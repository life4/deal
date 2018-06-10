Deal
====

.. figure:: logo.png
   :alt: Deal Logo

   Deal Logo

|Build Status| |Coverage Status| |PyPI version| |Development Status|
|Code size| |License|

**Deal** -- python library for `design by
contract <https://en.wikipedia.org/wiki/Design_by_contract>`__ (DbC)
programming.

This library contain 3 main conception from DbC:

-  `Precondition <https://en.wikipedia.org/wiki/Precondition>`__ --
   condition that must be true before function is executed.
-  `Postcondition <https://en.wikipedia.org/wiki/Postcondition>`__ --
   condition that must be true after function executed.
-  `Invariant <https://en.wikipedia.org/wiki/Invariant>`__ -- condition
   that can be relied upon to be true during execution of a program. In
   this library invariant condition check in 3 cases:

   1. Before class method execution.
   2. After class method execution.
   3. After some class attribute setting.

Features
--------

-  Functional declaration.
-  Custom exceptions.
-  Raising exceptions from contract.
-  Django Forms styled validators.
-  Attribute setting invariant validation.
-  Dynamically assigned attributes and methods invariant validation.

Installation
------------

Stable:

.. code:: bash

    pip install deal

Dev:

.. code:: bash

    pip install -e git+https://github.com/orsinium/deal.git#egg=deal

TL;DR
-----

-  ``@pre`` -- validate function arguments (pre-validation).
-  ``@post`` -- validate function result (post-validation).
-  ``@inv`` -- validate class methods before and after some method
   calling and after attribute setting.

Exceptions structure:
---------------------

-  ContractError (inherited from built-in AssertionError)

   -  PreContractError
   -  PostContractError
   -  InvContractError

Library decorators doesn't catch any exceptions raised from contracts.

Usage
-----

Contract types
~~~~~~~~~~~~~~

Pre (``pre``, ``require``):

.. code:: python

    In [1]: from deal import pre, post, inv, Scheme

    In [2]: @pre(lambda *args: all(map(lambda x: x > 0, args)))
       ...: def my_sum(*args):
       ...:     return sum(args)
       ...:

    In [3]: my_sum(2, 3, 4)
    Out[3]: 9

    In [4]: my_sum(2, -3, 4)
    PreContractError:

Post (``post``, ``ensure``):

.. code:: python

    In [1]: @post(lambda x: x > 0)
       ...: def my_sum(*args):
       ...:     return sum(args)
       ...:

    In [2]: my_sum(2, -3, 4)
    Out[2]: 3

    In [3]: my_sum(2, -3, -4)
    PostContractError:

Inv (``inv``, ``invariant``):

.. code:: python

    In [1]: @inv(lambda obj: obj.x > 0)
       ...: class A:
       ...:     x = 4
       ...:     

    In [2]: a = A()

    In [3]: a.x = 10

    In [4]: a.x = -10
    InvContractError:

    In [5]: A
    Out[5]: deal.core.AInvarianted

Customize error message
~~~~~~~~~~~~~~~~~~~~~~~

Custom message:

.. code:: python

    In [1]: @pre(lambda x: x > 0, "x must be > 0")
       ...: def f(x):
       ...:     return x * 2
       ...:

    In [2]: f(-2)
    PreContractError: x must be > 0

Custom exception:

.. code:: python

    In [1]: @pre(lambda x: x > 0, exception=AssertionError("x must be > 0"))
       ...: def f(x):
       ...:     return x * 2
       ...:

    In [2]: f(-2)
    AssertionError: x must be > 0

Return error message from contract:

.. code:: python

    In [1]: @pre(lambda x: x > 0 or "x must be > 0")
       ...: def f(x):
       ...:     return x * 2
       ...:

    In [2]: f(-5)
    PreContractError: x must be > 0

Validators
~~~~~~~~~~

1. Regular contract with errors returning:

.. code:: python

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

2. Simple validator (nearly Django Forms style, except initialization):

.. code:: python

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

3. Scheme like simple validator but ``data`` attribute contains
   dictionary with all passed arguments:

.. code:: python


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

Scheme automatically detect all arguments names:

.. code:: python

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

4. You can use any validators from
   `djburger <https://github.com/orsinium/djburger>`__. See `validators
   documentation <https://djburger.readthedocs.io/en/latest/validators.html>`__
   and `list of supported external
   libraries <https://github.com/orsinium/djburger#external-libraries-support>`__.
   For example, deal + djburger +
   `marshmallow <https://marshmallow.readthedocs.io/en/latest/>`__:

.. code:: python

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

Djburger is Django independent. You can use it in any python projects.

Contracts chaining
~~~~~~~~~~~~~~~~~~

You can chain any contracts:

.. code:: python

    In [1]: @pre(lambda x: x > 0)
       ...: @pre(lambda x: x < 10)
       ...: def f(x):
       ...:     return x * 2
       ...:

    In [2]: f(5)
    Out[2]: 10

    In [3]: f(-1)
    PreContractError:

    In [3]: f(12)
    PreContractError:

Chaining order:

-  ``@inv``: from top to bottom.
-  ``@pre``: from top to bottom.
-  ``@post``: from bottom to top.

Perfomance
----------

**NOTICE**: ``1 µs == 1000 ns``

``@pre`` and ``@post``:

.. code:: python

    In [1]: f = lambda x: x

    In [2]: pre_f = pre(lambda x: True)(f)

    In [3]: post_f = post(lambda x: True)(f)

    In [4]: %timeit f(10)
    92.3 ns ± 3.62 ns per loop (mean ± std. dev. of 7 runs, 10000000 loops each)

    In [5]: %timeit pre_f(10)
    2.07 µs ± 92.5 ns per loop (mean ± std. dev. of 7 runs, 100000 loops each)

    In [6]: %timeit post_f(10)
    2.03 µs ± 18.6 ns per loop (mean ± std. dev. of 7 runs, 100000 loops each)

+1 µs

``@inv``:

.. code:: python

    In [1]: class A:
       ...:     x = 4
       ...:     

    In [2]: InvA = inv(lambda obj: True)(A)

    In [3]: a = A()

    In [4]: inv_a = InvA()

    In [5]: %timeit a.x = 10
    76.4 ns ± 1.36 ns per loop (mean ± std. dev. of 7 runs, 10000000 loops each)

    In [6]: %timeit inv_a.x = 10
    6.89 µs ± 408 ns per loop (mean ± std. dev. of 7 runs, 100000 loops each)

+6 µs

Changelog
---------

**1.0.** ``@pre``, ``@post``, ``@inv``, error messages customization.

**1.1.** ``@inv`` chaining.

**1.2.** `Travis CI <https://travis-ci.org/orsinium/deal>`__, `wrapper
updating <https://docs.python.org/3/library/functools.html#functools.update_wrapper>`__.

**2.0.** `Schemes <#validators>`__,
`djburger <https://github.com/orsinium/djburger>`__ validators support.

Contributors
------------

-  `orsinium <https://github.com/orsinium/>`__
-  `Inokenty90 <https://github.com/Inokenty90/>`__

.. |Build Status| image:: https://travis-ci.org/orsinium/deal.svg?branch=master
   :target: https://travis-ci.org/orsinium/deal
.. |Coverage Status| image:: https://coveralls.io/repos/github/orsinium/deal/badge.svg
   :target: https://coveralls.io/github/orsinium/deal
.. |PyPI version| image:: https://img.shields.io/pypi/v/deal.svg
   :target: https://pypi.python.org/pypi/deal
.. |Development Status| image:: https://img.shields.io/pypi/status/deal.svg
   :target: https://pypi.python.org/pypi/deal
.. |Code size| image:: https://img.shields.io/github/languages/code-size/orsinium/deal.svg
   :target: https://github.com/orsinium/deal
.. |License| image:: https://img.shields.io/pypi/l/deal.svg
   :target: LICENSE
