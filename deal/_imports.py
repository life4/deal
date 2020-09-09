# built-in
import ast
import sys
from types import ModuleType
from typing import Any, Callable, List, Optional

# project
from _frozen_importlib_external import PathFinder

# app
from . import _aliases
from ._state import state
from .linter._extractors.common import get_name


class DealFinder(PathFinder):
    @classmethod
    def find_spec(cls, *args, **kwargs):
        spec = super().find_spec(*args, **kwargs)
        if spec is not None:  # pragma: no cover
            spec.loader = DealLoader(spec.loader)
        return spec


class DealLoader:
    __slots__ = ('_loader', )

    def __init__(self, loader):
        self._loader = loader

    def __getattr__(self, name: str):
        return getattr(self._loader, name)

    def exec_module(self, module: ModuleType) -> None:
        if not hasattr(self._loader, 'get_source'):
            return self._loader.exec_module(module)

        # get nodes with module-level contracts from the source code
        source = self._loader.get_source(module.__name__)
        if source is None:
            return self._loader.exec_module(module)
        tree = ast.parse(source)
        nodes = self._get_contracts(tree=tree)
        if not nodes:
            return self._loader.exec_module(module)

        # convert contracts nodes into real contracts
        contracts = []
        for node in nodes:
            contract = self._exec_contract(node=node)
            if contract is None:
                msg = 'unsupported contract: {}'.format(ast.dump(node))
                raise RuntimeError(msg)
            contracts.append(contract)

        # execute module with contracts
        wrapped = _aliases.chain(*contracts)(self._loader.exec_module)
        wrapped(module)

    @staticmethod
    def _get_contracts(tree: ast.Module) -> List[ast.AST]:
        for node in tree.body:  # type: Any
            if type(node) is not ast.Expr:
                continue
            if type(node.value) is not ast.Call:
                continue
            if get_name(node.value.func) != 'deal.module_load':
                continue
            return node.value.args
        return []

    @classmethod
    def _exec_contract(cls, node: ast.AST) -> Optional[Callable]:
        """Get AST node and return a contract function
        """
        if type(node) is ast.Call and not node.args:    # type: ignore
            return cls._exec_contract(node.func)()      # type: ignore

        if not isinstance(node, ast.Attribute):
            return None
        if node.value.id != 'deal':  # type: ignore
            return None
        contract = getattr(_aliases, node.attr, None)
        if contract is None:
            return None
        return contract


def module_load(*contracts) -> None:
    """
    Specify contracts that will be checked at module import time.
    Keep in mind that [deal.activate](#deal.activate) must be called
    before importing a module with `module_load` contract.

    ```pycon
    >>> import deal
    >>> deal.module_load(deal.has(), deal.safe)

    ```

    See [Contracts for importing modules](./module_load.md)
    documentation for more details.
    """
    if not state.debug:
        return
    if not contracts:
        raise RuntimeError('no contracts specified')
    if DealFinder not in sys.meta_path:
        msg = 'deal.activate must be called '
        msg += 'before importing anything with deal.module_load contract'
        raise RuntimeError(msg)


def activate() -> bool:
    """Activate module-level checks.

    This function must be called before importing anything
    with [deal.module_load](#deal.module_load) contract.
    Otherwise, the contract won't be executed.

    The best practice is to place it in `__init__.py` of your project:

    ```pycon
    >>> import deal
    >>> deal.activate()

    ```

    See [Contracts for importing modules](./module_load.md)
    documentation for more details.
    """
    if not state.debug:
        return False
    if DealFinder in sys.meta_path:
        return False
    index = sys.meta_path.index(PathFinder)
    sys.meta_path[index] = DealFinder  # type: ignore
    return True


def deactivate() -> bool:
    """used in tests
    """
    if DealFinder not in sys.meta_path:
        return False
    index = sys.meta_path.index(DealFinder)  # type: ignore
    sys.meta_path[index] = PathFinder
    return True
