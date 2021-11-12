from pathlib import Path
from typing import List, NamedTuple, Optional, Set
from .._cached_property import cached_property
from ._contract import Category
from ._func import Func
from ._rules import CheckRaises


class Mutation(NamedTuple):
    line: int
    contract: Category
    args: List[str]
    indent: int

    def __str__(self):
        args = ', '.join(self.args)
        dec = f'@deal.{self.contract.value}({args})'
        return ' ' * self.indent + dec


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
        mut = self._mutation_excs(func)
        if mut is not None:
            self.mutations.append(mut)

    def _mutation_excs(self, func: Func) -> Optional[Mutation]:
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
        if not excs:
            return None
        return Mutation(
            line=func.line,
            indent=func.col,
            contract=Category.RAISES,
            args=sorted(excs),
        )

    def _apply_mutations(self, content: str) -> str:
        if not self.mutations:
            return content
        lines = content.splitlines(keepends=True)
        self.mutations.sort(key=lambda x: x.line, reverse=True)
        for mutation in self.mutations:
            lines.insert(mutation.line - 1, f'{mutation}\n')
        return ''.join(lines)
