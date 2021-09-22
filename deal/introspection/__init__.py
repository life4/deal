"""
The module provides `get_contracts` function which enumerates
contracts wrapping the given function. Every contract is returned
in wrapper providing a stable interface.
"""

from ._wrappers import Contract, Pre, Post, Ensure, Raises, Reason, Has
from ._extractor import get_contracts

__all__ = [
    'Contract',
    'Ensure',
    'Has',
    'Post',
    'Pre',
    'Raises',
    'Reason',
    'get_contracts',
]
