# This file is excluded from coverage.

from importlib import import_module

import deal
from deal._runtime import Validator


# will be filled from the linter
contract = ...
func = ...


def inject(name: str) -> bool:
    """Import the given module and inject it into globals.
    """
    try:
        globals()[name] = import_module(name)
    except ImportError:
        return False
    return True


def validate(args, kwargs) -> None:
    """Run validator, trying to fix missed imports on the way.
    """
    base = Validator(validator=contract, exception=deal.ContractError)
    if func is not Ellipsis:
        base.function = func

    old_name = None
    for _ in range(10):  # maximum 10 tries, just in case
        try:
            base.validate(args, kwargs)
            return
        except NameError as err:
            # Oh no, we didn't properly inject a variable,
            # and now it is missed. Let's try to import it
            # as module and run the contract again.

            name = err.args[0].split("'")[1]
            # the missed name haven't changed, injection didn't help
            if name == old_name:
                raise
            # try to import missed module
            ok = inject(name)
            # the missed name is not a module, give up
            if not ok:
                raise
            continue


try:
    validate(args, kwargs)  # type: ignore  # noqa: F821
except deal.ContractError as exc:
    result = False
    if exc.args:
        result = exc.args[0]
else:
    result = True
