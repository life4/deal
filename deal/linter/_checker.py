from __future__ import annotations

import ast
from pathlib import Path
import re
import tokenize
from typing import Iterator

from astroid import AstroidSyntaxError

from .. import __version__
from ._error import Error
from ._func import Func
from ._rules import FuncRule, ModuleRule, rules
from ._stub import StubsManager


# based on regex from the source code of flake8
RE_NOQA = re.compile(
    r'# noqa(?::[\s]?(?P<codes>([A-Z]+[0-9]*(?:[,\s]+)?)+))?',
    re.IGNORECASE,
)
RE_DIGITS = re.compile(r'[0-9]+')
PREFIXES = ('DEAL', 'DEA1', 'DEL', 'DEA', 'DIL')


class Checker:
    """The entry point for the linter, compatible with flake8 plugins interface.
    """
    __slots__ = ('_tree', '_filename', '_tokens', '_stubs')
    name = 'deal'
    version = __version__
    _rules = rules

    def __init__(
        self,
        tree: ast.Module,
        file_tokens: list[tokenize.TokenInfo] | None = None,
        filename: str = 'stdin',
    ) -> None:
        self._tree = tree
        self._filename = filename
        self._tokens = file_tokens

        paths = list(StubsManager.default_paths)
        if filename != 'stdin':
            paths.append(Path(filename).absolute().parent)
        self._stubs = StubsManager(paths=paths)

    @classmethod
    def from_path(cls, path: Path) -> Checker:
        source = path.read_text()
        with path.open('rb') as stream:
            tokens = list(tokenize.tokenize(stream.readline))
        return cls(
            tree=ast.parse(source),
            file_tokens=tokens,
            filename=str(path),
        )

    def run(self) -> Iterator[tuple]:
        for error in self.get_errors():
            yield tuple(error) + (type(self),)

    def get_funcs(self) -> list[Func]:
        if self._filename == 'stdin':
            return Func.from_ast(tree=self._tree)
        try:
            return Func.from_path(path=Path(self._filename))
        except AstroidSyntaxError:
            return Func.from_ast(tree=self._tree)

    def get_errors(self) -> Iterator[Error]:
        reported = set()
        for func in self.get_funcs():
            for rule in self._rules:
                if not isinstance(rule, FuncRule):
                    continue
                for error in rule(func=func, stubs=self._stubs):
                    hs = hash(error)
                    if hs in reported:
                        continue
                    noqa = self._get_noqa(error.row)
                    if f'{error.code:03d}'.startswith(noqa):
                        continue
                    reported.add(hs)
                    yield error

        for rule in self._rules:
            if not isinstance(rule, ModuleRule):
                continue
            yield from rule(tree=self._tree)

    def _get_noqa(self, line_number: int) -> tuple[str, ...]:
        """Extract codes defined in `noqa` comments (with DEAL prefix removed).
        """
        comment = self._get_comment(line_number)
        if not comment:
            return ()
        match = RE_NOQA.search(comment)
        if match is None:
            return ()
        raw_codes = (match.group('codes') or '').split(',')
        clean_codes = []
        for code in raw_codes:
            code = code.strip().upper()
            if not code.startswith(PREFIXES):
                print(repr(code), match)
                continue
            match = RE_DIGITS.search(code)
            clean_codes.append(match.group(0) if match else '')
        return tuple(clean_codes)

    def _get_comment(self, line_number: int) -> str | None:
        if self._tokens is None:
            return None
        for token in self._tokens:
            if token.start[0] != line_number:
                continue
            if token.type != tokenize.COMMENT:
                continue
            return token.string
        return None
