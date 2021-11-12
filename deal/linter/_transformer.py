from pathlib import Path
from typing import Iterator, List, NamedTuple, Set, Tuple, Union
from .._cached_property import cached_property
from ._contract import Category
from ._func import Func
from ._rules import CheckRaises


Priority = int


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


class Transformer:
    path: Path
    mutations: List[Mutation]

    def __init__(self, path: Path) -> None:
        self.path = path
        self.mutations = []

    @cached_property
    def funcs(self) -> List[Func]:
        return Func.from_path(self.path)

    def transform(self) -> str:
        for func in self.funcs:
            self._collect_mutations(func)
        content = self.path.read_text()
        return self._apply_mutations(content)

    def _collect_mutations(self, func: Func) -> None:
        for mut in self._mutations_excs(func):
            self.mutations.append(mut)

    def _mutations_excs(self, func: Func) -> Iterator[Mutation]:
        checker = CheckRaises()
        excs: Set[str] = set()
        cats = {Category.RAISES, Category.SAFE, Category.PURE}
        declared = []
        for contract in func.contracts:
            if contract.category not in cats:
                continue
            declared.extend(contract.exceptions)
        for error in checker.get_undeclared(func, declared):
            assert isinstance(error.value, str)
            excs.add(error.value)

        # if no new exceptions found, add deal.safe
        if not excs:
            if declared:
                return
            for contract in func.contracts:
                if contract.category in {Category.PURE, Category.SAFE}:
                    return
            yield Insert(
                line=func.line,
                indent=func.col,
                contract=Category.SAFE,
                args=[],
            )
            return

        # if new exceptions detected, remove old contracts and add a new deal.raises
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

    def _apply_mutations(self, content: str) -> str:
        if not self.mutations:
            return content
        lines = content.splitlines(keepends=True)
        self.mutations.sort(key=lambda x: x.key, reverse=True)
        for mutation in self.mutations:
            mutation.apply(lines)
        return ''.join(lines)
