from __future__ import annotations

from enum import Enum
from pathlib import Path
from typing import Iterator, NamedTuple, Union

import astroid

from ._contract import Category
from ._extractors import get_value
from ._func import Func
from ._rules import CheckMarkers, CheckRaises


Priority = int


class TransformationType(Enum):
    RAISES = 'raises'
    HAS = 'has'
    SAFE = 'safe'
    PURE = 'pure'
    IMPORT = 'import'


class AppendText(NamedTuple):
    line: int
    text: str

    def apply(self, lines: list[str]) -> None:
        content = lines[self.line - 1]
        content = content.rstrip('\n')
        content += f'{self.text}\n'
        lines[self.line - 1] = content

    @property
    def key(self) -> tuple[int, Priority]:
        return (self.line, 1)


class InsertText(NamedTuple):
    line: int
    text: str

    def apply(self, lines: list[str]) -> None:
        lines.insert(self.line - 1, f'{self.text}\n')

    @property
    def key(self) -> tuple[int, Priority]:
        return (self.line, 2)


class InsertContract(NamedTuple):
    line: int
    contract: Category
    args: list[str]
    indent: int

    def apply(self, lines: list[str]) -> None:
        lines.insert(self.line - 1, f'{self}\n')

    @property
    def key(self) -> tuple[int, Priority]:
        return (self.line, 3)

    def __str__(self) -> str:
        args = ', '.join(self.args)
        if not self.args and self.contract.brackets_optional:
            dec = f'@deal.{self.contract.value}'
        else:
            dec = f'@deal.{self.contract.value}({args})'
        return ' ' * self.indent + dec


class Remove(NamedTuple):
    line: int

    def apply(self, lines: list[str]) -> None:
        lines.pop(self.line - 1)

    @property
    def key(self) -> tuple[int, Priority]:
        return (self.line, 4)


Mutation = Union[AppendText, InsertText, InsertContract, Remove]


class Transformer(NamedTuple):
    """Transformer adds deal decorators into the given script.
    """
    content: str
    path: Path
    types: set[TransformationType]
    mutations: list[Mutation] = []
    quote: str = "'"

    def transform(self) -> str:
        self.mutations.clear()
        tree = astroid.parse(self.content, path=self.path)
        for func in Func.from_astroid(tree):
            self._collect_mutations(func)
        self.mutations.extend(self._mutations_pure())
        self.mutations.extend(self._mutations_import(tree))
        return self._apply_mutations(self.content)

    def _collect_mutations(self, func: Func) -> None:
        self.mutations.extend(self._mutations_excs(func))
        self.mutations.extend(self._mutations_markers(func))
        self.mutations.extend(self._mutations_property(func))

    def _mutations_excs(self, func: Func) -> Iterator[Mutation]:
        """Add @deal.raises or @deal.safe if needed.
        """
        cats = {Category.RAISES, Category.SAFE, Category.PURE}

        # collect declared exceptions
        declared: list[Union[str, type]] = []
        for contract in func.contracts:
            if contract.category not in cats:
                continue
            declared.extend(contract.exceptions)

        # collect undeclared exceptions
        excs: set[str] = set()
        for error in CheckRaises().get_undeclared(func, declared):
            assert isinstance(error.value, str)
            excs.add(error.value)

        # if no new exceptions found, add deal.safe
        if not excs:
            if declared:
                return
            if self._disabled(TransformationType.SAFE, TransformationType.PURE):
                return
            if func.has_contract(Category.PURE, Category.SAFE):
                return
            yield InsertContract(
                line=self._get_insert_line(func),
                indent=func.col,
                contract=Category.SAFE,
                args=[],
            )
            return

        # if new exceptions detected, remove old contracts and add a new deal.raises
        if self._disabled(TransformationType.RAISES):
            return
        for contract in func.contracts:
            if contract.category not in cats:
                continue
            yield Remove(contract.line)
            if contract.category == Category.PURE:
                yield InsertContract(
                    line=self._get_insert_line(func),
                    indent=func.col,
                    contract=Category.HAS,
                    args=[],
                )
        contract_args = [self._exc_as_str(exc) for exc in declared]
        contract_args.extend(sorted(excs))
        yield InsertContract(
            line=self._get_insert_line(func),
            indent=func.col,
            contract=Category.RAISES,
            args=contract_args,
        )

    @staticmethod
    def _exc_as_str(exc) -> str:
        if isinstance(exc, str):
            return exc
        return exc.__name__

    def _mutations_markers(self, func: Func) -> Iterator[Mutation]:
        """Add @deal.has if needed.
        """
        if self._disabled(TransformationType.HAS, TransformationType.PURE):
            return
        cats = {Category.HAS, Category.PURE}

        # collect declared markers
        declared: list[str] = []
        for contract in func.contracts:
            if contract.category not in cats:
                continue
            for arg in contract.args:
                value = get_value(arg)
                if isinstance(value, str):
                    declared.append(value)

        # collect undeclared markers
        markers: set[str] = set()
        for error in CheckMarkers().get_undeclared(func, set(declared)):
            assert isinstance(error.value, str)
            markers.add(error.value)

        # if no new markers found, add deal.has()
        if not markers:
            if func.has_contract(Category.PURE, Category.HAS):
                return
            yield InsertContract(
                line=self._get_insert_line(func),
                indent=func.col,
                contract=Category.HAS,
                args=[],
            )
            return

        # if new markers detected, remove old contracts and add a new deal.has
        for contract in func.contracts:
            if contract.category not in cats:
                continue
            yield Remove(contract.line)
            if contract.category == Category.PURE:
                yield InsertContract(
                    line=self._get_insert_line(func),
                    indent=func.col,
                    contract=Category.SAFE,
                    args=[],
                )
        contract_args = [self._exc_as_str(marker) for marker in declared]
        contract_args.extend(sorted(markers))
        yield InsertContract(
            line=self._get_insert_line(func),
            indent=func.col,
            contract=Category.HAS,
            args=[f'{self.quote}{arg}{self.quote}' for arg in contract_args],
        )

    def _mutations_property(self, func: Func) -> Iterator[Mutation]:
        assert isinstance(func.node, astroid.FunctionDef)
        if func.node.decorators is None:
            return
        assert isinstance(func.node.decorators, astroid.Decorators)
        for decorator in func.node.decorators.nodes:
            if not isinstance(decorator, astroid.Name):
                continue
            if decorator.name not in {'property', 'cached_property'}:
                continue
            if not self._has_mutation_on_line(decorator.lineno + 1):
                continue
            yield AppendText(decorator.lineno, '  # type: ignore[misc]')

    def _has_mutation_on_line(self, line: int) -> bool:
        return any(mutation.line == line for mutation in self.mutations)

    def _mutations_import(self, tree: astroid.Module) -> Iterator[Mutation]:
        """Add `import deal` if needed.
        """
        if self._disabled(TransformationType.IMPORT):
            return
        if not self.mutations:
            return
        # check if already imported
        for stmt in tree.body:
            if not isinstance(stmt, astroid.Import):
                continue
            for name, _ in stmt.names:
                if name == 'deal':
                    return

        # We insert the import after `__future__` imports and module imports.
        # We don't skip `from` imports, though, because they can be multiline.
        line = 1
        for stmt in tree.body:
            if isinstance(stmt, astroid.Import):
                line = stmt.lineno + 1
            if isinstance(stmt, astroid.ImportFrom):
                if stmt.modname == '__future__':
                    line = stmt.lineno + 1
        yield InsertText(line=line, text='import deal')

    def _mutations_pure(self) -> Iterator[Mutation]:
        """Merge `@deal.safe` and `@deal.has` into `@deal.pure` if needed.
        """
        if self._disabled(TransformationType.PURE):
            return
        if not self.mutations:
            return

        # find lines that have both @deal.has and @deal.safe
        lines_has = set()
        lines_safe = set()
        for mut in self.mutations:
            if not isinstance(mut, InsertContract):
                continue
            if mut.contract == Category.HAS and mut.args == []:
                lines_has.add(mut.line)
            if mut.contract == Category.SAFE:
                lines_safe.add(mut.line)
        lines = lines_safe & lines_has

        # remove @deal.has and @deal.safe mutations, replace by @deal.pure
        old_cats = {Category.HAS, Category.SAFE}
        for mut in self.mutations.copy():
            if not isinstance(mut, InsertContract):
                continue
            if mut.line not in lines:
                continue
            assert mut.contract in old_cats, 'unexpected contract generated'
            self.mutations.remove(mut)
            if mut.contract == Category.SAFE:
                yield mut._replace(contract=Category.PURE)

        # If PURE tranformation is enabled,
        # we emit @deal.safe and @deal.has even if they are disabled, so they can be
        # merged into @deal.pure. So, if they are disabled and were not merged,
        # drop them here.
        if self._disabled(TransformationType.SAFE):
            for mut in self.mutations.copy():
                if isinstance(mut, InsertContract) and mut.contract == Category.SAFE:
                    self.mutations.remove(mut)
        if self._disabled(TransformationType.HAS):
            for mut in self.mutations.copy():
                if isinstance(mut, InsertContract) and mut.contract == Category.HAS:
                    self.mutations.remove(mut)

    @staticmethod
    def _get_insert_line(func: Func) -> int:
        assert isinstance(func.node, astroid.FunctionDef)
        line = func.line
        if func.node.decorators is None:
            return line
        assert isinstance(func.node.decorators, astroid.Decorators)
        for decorator in func.node.decorators.nodes:
            # some Python versions point to the first decorator, some to `def`
            if decorator.lineno < func.line:
                return func.line  # pragma: no cover
            if not isinstance(decorator, astroid.Name):
                continue
            if decorator.name in {'staticmethod', 'classmethod'}:
                continue
            line = decorator.lineno + 1
        return line

    def _apply_mutations(self, content: str) -> str:
        if not self.mutations:
            return content
        lines = content.splitlines(keepends=True)
        self.mutations.sort(key=lambda x: x.key, reverse=True)
        for mutation in self.mutations:
            mutation.apply(lines)
        return ''.join(lines)

    def _disabled(self, *expected: TransformationType) -> bool:
        """Check if all of the given types are disabled.
        """
        return not bool(self.types & set(expected))
