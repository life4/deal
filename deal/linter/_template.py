from deal import ContractError
from deal._decorators.base import Base

contract = ...
base = Base(validator=contract)

try:
    base.validate(*args, **kwargs)  # noqa: F821
except ContractError as exc:
    result = False
    if exc.args:
        result = exc.args[0]
else:
    result = True
