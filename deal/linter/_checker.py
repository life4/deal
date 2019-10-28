import ast
import typing

from ._error import Error
from ._func import Func
from ._rules import rules


class Checker:
    name = "deal"
    version = "1.0.0"
    _tree = None
    _rules = rules

    def __init__(self, tree: ast.AST, file_tokens=None, filename: str = 'stdin'):
        self._tree = tree
        self._filename = filename

    def run(self) -> typing.Iterator[tuple]:
        for error in self.get_errors():
            yield tuple(error) + (type(self),)  # type: ignore

    def get_errors(self) -> typing.Iterator[Error]:
        funcs = Func.from_tree(tree=self._tree)
        for func in funcs:
            for rule in self._rules:
                yield from rule(func)
