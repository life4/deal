"""
**Deal** is a Python library for [design by contract][wiki] (DbC) programming.
See [documentation][docs] for more details.

[wiki]: https://en.wikipedia.org/wiki/Design_by_contract
[docs]: https://deal.readthedocs.io/index.html
"""

# main package info
__title__ = 'deal'
__version__ = '4.7.2'
__author__ = 'Gram Orsinium'
__license__ = 'MIT'


from ._aliases import (
    chain, ensure, has, implies, inv, post, pre, pure, raises, reason, safe,
)
from ._exceptions import (
    ContractError, InvContractError, MarkerError, OfflineContractError, PostContractError,
    PreContractError, RaisesContractError, ReasonContractError, SilentContractError,
)
from ._imports import activate, module_load
from ._schemes import Scheme
from ._sphinx import AutoDoc
from ._state import disable, enable, reset
from ._testing import TestCase, cases


__all__ = [
    'AutoDoc',
    'cases',
    'Scheme',
    'TestCase',

    # state
    'disable',
    'enable',
    'reset',

    # decorators
    'chain',
    'ensure',
    'has',
    'inv',
    'post',
    'pre',
    'raises',
    'reason',

    # aliases
    'safe',
    'pure',
    'implies',

    # module level
    'module_load',
    'activate',

    # exceptions
    'ContractError',
    'InvContractError',
    'MarkerError',
    'OfflineContractError',
    'PostContractError',
    'PreContractError',
    'RaisesContractError',
    'ReasonContractError',
    'SilentContractError',
]
