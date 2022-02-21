import ast
import typing
from pathlib import Path

from astroid import AstroidSyntaxError

from .. import __version__
from ._error import Error
from ._func import Func
from ._rules import FuncRule, ModuleRule, rules
from ._stub import StubsManager


class Checker:
    __slots__ = ('_tree', '_filename', '_stubs')
    name = 'deal'
    version = __version__
    _rules = rules

    def __init__(self, tree: ast.Module, file_tokens=None, filename: str = 'stdin') -> None:
        self._tree = tree
        self._filename = filename

        paths = list(StubsManager.default_paths)
        if filename != 'stdin':
            paths.append(Path(filename).absolute().parent)
        self._stubs = StubsManager(paths=paths)

    def run(self) -> typing.Iterator[tuple]:
        for error in self.get_errors():
            yield tuple(error) + (type(self),)

    def get_funcs(self) -> typing.List['Func']:
        if self._filename == 'stdin':
            return Func.from_ast(tree=self._tree)
        try:
            return Func.from_path(path=Path(self._filename))
        except AstroidSyntaxError:
            return Func.from_ast(tree=self._tree)

    def get_errors(self) -> typing.Iterator[Error]:
        reported = set()
        for func in self.get_funcs():
            for rule in self._rules:
                if not isinstance(rule, FuncRule):
                    continue
                for error in rule(func=func, stubs=self._stubs):
                    hs = hash(error)
                    if hs in reported:
                        continue
                    reported.add(hs)
                    yield error

        for rule in self._rules:
            if not isinstance(rule, ModuleRule):
                continue
            yield from rule(tree=self._tree)
