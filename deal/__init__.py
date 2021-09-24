"""
**Deal** is a Python library for [design by contract][wiki] (DbC) programming.
See [documentation] for more details.

[wiki]: https://en.wikipedia.org/wiki/Design_by_contract
[documentation]: https://deal.readthedocs.io/index.html
"""
from . import introspection
from ._aliases import (
    chain, dispatch, ensure, has, implies, inv, post, pre, pure, raises, reason, safe,
)
from ._exceptions import (
    ContractError, InvContractError, MarkerError, NoMatchError,
    OfflineContractError, PostContractError, PreContractError,
    RaisesContractError, ReasonContractError, SilentContractError,
)
from ._imports import activate, module_load
from ._schemes import Scheme
from ._sphinx import autodoc
from ._state import disable, enable, reset
from ._testing import TestCase, cases


__title__ = 'deal'
__version__ = '4.10.0'
__author__ = 'Gram (@orsinium)'
__license__ = 'MIT'
__all__ = [
    'autodoc',
    'cases',
    'Scheme',
    'TestCase',
    'introspection',

    # state
    'disable',
    'enable',
    'reset',

    # decorators
    'chain',
    'dispatch',
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
    'NoMatchError',
    'OfflineContractError',
    'PostContractError',
    'PreContractError',
    'RaisesContractError',
    'ReasonContractError',
    'SilentContractError',
]
