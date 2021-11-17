from enum import Enum
from pathlib import Path
from typing import Iterator, List, NamedTuple, Set, Tuple, Union

import astroid
from ._contract import Category
from ._func import Func
from ._rules import CheckRaises, CheckMarkers
from ._extractors import get_value


Priority = int


class TransformationType(Enum):
    RAISES = 'raises'
    HAS = 'has'
    SAFE = 'safe'


class Insert(NamedTuple):
    line: int
    contract: Category
    args: List[str]
    indent: int

    def apply(self, lines: List[str]) -> None:
        lines.insert(self.line - 1, f'{self}\n')

    @property
    def key(self) -> Tuple[int, Priority]:
        return (self.line, 1)

    def __str__(self) -> str:
        args = ', '.join(self.args)
        if not self.args and self.contract.brackets_optional:
            dec = f'@deal.{self.contract.value}'
        else:
            dec = f'@deal.{self.contract.value}({args})'
        return ' ' * self.indent + dec


class Remove(NamedTuple):
    line: int

    def apply(self, lines: List[str]) -> None:
        lines.pop(self.line - 1)

    @property
    def key(self) -> Tuple[int, Priority]:
        return (self.line, 2)


Mutation = Union[Insert, Remove]


class Transformer(NamedTuple):
    content: str
    path: Path
    types: Set[TransformationType]
    mutations: List[Mutation] = []
    quote: str = "'"

    def transform(self) -> str:
        self.mutations.clear()
        tree = astroid.parse(self.content, path=self.path)
        for func in Func.from_astroid(tree):
            self._collect_mutations(func)
        return self._apply_mutations(self.content)

    def _collect_mutations(self, func: Func) -> None:
        self.mutations.extend(self._mutations_excs(func))
        self.mutations.extend(self._mutations_markers(func))

    def _mutations_excs(self, func: Func) -> Iterator[Mutation]:
        cats = {Category.RAISES, Category.SAFE, Category.PURE}

        # collect declared exceptions
        declared: List[Union[str, type]] = []
        for contract in func.contracts:
            if contract.category not in cats:
                continue
            declared.extend(contract.exceptions)

        # collect undeclared exceptions
        excs: Set[str] = set()
        for error in CheckRaises().get_undeclared(func, declared):
            assert isinstance(error.value, str)
            excs.add(error.value)

        # if no new exceptions found, add deal.safe
        if not excs:
            if declared:
                return
            if TransformationType.SAFE not in self.types:
                return
            if func.has_contract(Category.PURE, Category.SAFE):
                return
            yield Insert(
                line=func.line,
                indent=func.col,
                contract=Category.SAFE,
                args=[],
            )
            return

        # if new exceptions detected, remove old contracts and add a new deal.raises
        if TransformationType.RAISES not in self.types:
            return
        for contract in func.contracts:
            if contract.category not in cats:
                continue
            yield Remove(contract.line)
            if contract.category == Category.PURE:
                yield Insert(
                    line=func.line,
                    indent=func.col,
                    contract=Category.HAS,
                    args=[],
                )
        contract_args = [self._exc_as_str(exc) for exc in declared]
        contract_args.extend(sorted(excs))
        yield Insert(
            line=func.line,
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
        if TransformationType.HAS not in self.types:
            return
        cats = {Category.HAS, Category.PURE}

        # collect declared markers
        declared: List[str] = []
        for contract in func.contracts:
            if contract.category not in cats:
                continue
            declared.extend(get_value(arg) for arg in contract.args)

        # collect undeclared markers
        markers: Set[str] = set()
        for error in CheckMarkers().get_undeclared(func, set(declared)):
            assert isinstance(error.value, str)
            markers.add(error.value)

        # if no new markers found, add deal.has()
        if not markers:
            if func.has_contract(Category.PURE, Category.HAS):
                return
            yield Insert(
                line=func.line,
                indent=func.col,
                contract=Category.HAS,
                args=[],
            )
            return

        # if new markers detected, remove old contracts and add a new deal.raises
        for contract in func.contracts:
            if contract.category not in cats:
                continue
            yield Remove(contract.line)
            if contract.category == Category.PURE:
                yield Insert(
                    line=func.line,
                    indent=func.col,
                    contract=Category.SAFE,
                    args=[],
                )
        contract_args = [self._exc_as_str(marker) for marker in declared]
        contract_args.extend(sorted(markers))
        yield Insert(
            line=func.line,
            indent=func.col,
            contract=Category.HAS,
            args=[f'{self.quote}{arg}{self.quote}' for arg in contract_args],
        )

    def _apply_mutations(self, content: str) -> str:
        if not self.mutations:
            return content
        lines = content.splitlines(keepends=True)
        self.mutations.sort(key=lambda x: x.key, reverse=True)
        for mutation in self.mutations:
            mutation.apply(lines)
        return ''.join(lines)
