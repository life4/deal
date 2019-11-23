# built-in
import ast
import sys
from _frozen_importlib_external import PathFinder
from typing import Callable, Optional

from .linter._extractors.common import get_name
from . import _aliases


class DealFinder(PathFinder):
    @classmethod
    def find_spec(cls, *args, **kwargs):
        spec = super().find_spec(*args, **kwargs)
        if spec is not None:
            spec.loader = DealLoader(spec.loader)
        return spec


class DealLoader:
    def __init__(self, loader):
        self._loader = loader

    def __getattr__(self, name):
        return getattr(self._loader, name)

    def exec_module(self, module) -> None:
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
                msg = 'unsupported contract: {}'.format(ast.dump(contract))
                raise RuntimeError(msg)
            contracts.append(contract)

        # execute module with contracts
        wrapped = _aliases.chain(contract)(self._loader.exec_module)
        wrapped(module)

    @staticmethod
    def _get_contracts(tree) -> Optional[list]:
        for node in tree.body:
            if not type(node) is ast.Expr:
                continue
            if not type(node.value) is ast.Call:
                continue
            if get_name(node.value.func) != 'deal.load':
                continue
            return node.value.args
        return []

    @staticmethod
    def _exec_contract(node) -> Optional[Callable]:
        if not isinstance(node, ast.Attribute):
            return None
        if node.value.id != 'deal':
            return None
        contract = getattr(_aliases, node.attr, None)
        if contract is None:
            return None
        return contract


def load(*contracts) -> None:
    return


def register():
    if DealFinder in sys.meta_path:
        return
    index = sys.meta_path.index(PathFinder)
    sys.meta_path[index] = DealFinder
