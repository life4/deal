# This file is excluded from coverage.

from deal import ContractError
from deal._decorators.base import Base

# will be filled from the linter
contract = ...
func = ...

base = Base(validator=contract)
if func is not Ellipsis:
    base.function = func

try:
    base.validate(*args, **kwargs)  # noqa: F821
except ContractError as exc:
    result = False
    if exc.args:
        result = exc.args[0]
else:
    result = True
