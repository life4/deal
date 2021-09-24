# Contracts for modules

The function `module_load` allows you to control what can happen at module load stage.

Usage:

1. Call `deal.activate()` before importing anything.
1. Call `deal.module_load()` in any place at module level in all modules that should be tested. Pass inside all contracts that should be controlled. By design, only contracts from deal without arguments are supported.

## Example

`__init__.py`:

```python
import deal

deal.activate()

from .other import something
```

`other.py`:

```python
import deal
import something_else

deal.module_load(deal.pure)

something = 1
print(1)  # contract violation! deal.SilentContractError will be raised
```

## How it works

1. Calling `deal.activate` registers [import finder and loader](https://docs.python.org/3/reference/import.html#finders-and-loaders). From now, all imported files will be checked by deal.
1. The loader reads imported file, generates [AST](https://docs.python.org/3/library/ast.html) for it, and looks for `deal.module_load` calling.
1. If loader found `deal.module_load` in the module, it extracts contracts from it.
1. If all contracts are valid (imported from deal and have no arguments), loader loads the module with contracts activated.

## Motivation

This contract is inspired by article [Python at Scale: Strict Modules](https://instagram-engineering.com/python-at-scale-strict-modules-c0bb9245c834). A module loading should be fast, pure, and safe. This function allows to enforce it.
