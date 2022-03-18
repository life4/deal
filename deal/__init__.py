"""
**Deal** is a Python library for [design by contract][wiki] (DbC) programming.
See [documentation] for more details.

[wiki]: https://en.wikipedia.org/wiki/Design_by_contract
[documentation]: https://deal.readthedocs.io/index.html
"""
from . import introspection
from ._exceptions import (
    ContractError, ExampleContractError, InvContractError, MarkerError,
    NoMatchError, OfflineContractError, PostContractError, PreContractError,
    RaisesContractError, ReasonContractError, SilentContractError,
)
from ._imports import activate, module_load
from ._runtime import (
    catch, chain, dispatch, ensure, example, has, implies,
    inherit, inv, post, pre, pure, raises, reason, safe,
)
from ._schemes import Scheme
from ._sphinx import autodoc
from ._state import disable, enable, reset
from ._testing import TestCase, cases


__title__ = 'deal'
__version__ = '4.21.1'
__author__ = 'Gram (@orsinium)'
__license__ = 'MIT'
__all__ = [
    'autodoc',
    'cases',
    'introspection',
    'Scheme',
    'TestCase',

    # state
    'disable',
    'enable',
    'reset',

    # decorators
    'chain',
    'dispatch',
    'ensure',
    'example',
    'has',
    'inherit',
    'inv',
    'post',
    'pre',
    'raises',
    'reason',

    # aliases
    'catch',
    'implies',
    'pure',
    'safe',

    # module level
    'module_load',
    'activate',

    # exceptions
    'ContractError',
    'ExampleContractError',
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
