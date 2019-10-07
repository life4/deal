"""
**Deal** -- python library for design by contract (DbC) programming.
https://en.wikipedia.org/wiki/Design_by_contract

This library contain 3 main conception from DbC:

* Precondition -- condition that must be true before function is executed.
* Postcondition -- condition that must be true after function executed.
* Invariant -- condition that can be relied upon to be true during execution
  of a program. In this library invariant condition check in 3 cases:
    1. Before class method execution.
    2. After class method execution.
    3. After some class attribute setting.
"""

# main package info
__title__ = 'deal'
__version__ = '3.1.0'
__author__ = 'Gram Orsinium'
__license__ = 'MIT'


from ._aliases import *              # noQA
from ._exceptions import *           # noQA
from ._schemes import Scheme
from ._state import reset, switch
from ._testing import cases, TestCase

__all__ = [
    'cases',
    'reset',
    'Scheme',
    'switch',
    'TestCase',
]
