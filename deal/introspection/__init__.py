"""
The module provides `get_contracts` function which enumerates
contracts wrapping the given function. Every contract is returned
in wrapper providing a stable interface.

Usage example:

```python
import deal

@deal.pre(lambda x: x > 0)
def f(x):
    return x + 1

contracts = deal.introspection.get_contracts(f)
for contract in contracts:
    assert isinstance(contract, deal.introspection.Contract)
    assert isinstance(contract, deal.introspection.Pre)
    assert contract.source == 'x > 0'
    assert contract.exception is deal.PreContractError
    contract.validate(1)
```
"""

from ._extractor import get_contracts, init_all, unwrap
from ._wrappers import (
    Contract, Ensure, Example, Has, Post, Pre, Raises, Reason, ValidatedContract,
)


__all__ = [
    # functions
    'get_contracts',
    'init_all',
    'unwrap',

    # wrappers
    'Contract',
    'Ensure',
    'Example',
    'Has',
    'Post',
    'Pre',
    'Raises',
    'Reason',
    'ValidatedContract',
]
