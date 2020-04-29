import json
from pathlib import Path
from typing import Any, Dict, FrozenSet, Iterator, Optional, Sequence

import astroid


EXTENSION = '.json'


class StubFile:

    def __init__(self, path: Path) -> None:
        self.path = path
        self._content = dict()  # type: Dict[str, Dict[str, Any]]

    def load(self) -> None:
        with self.path.open(encoding='utf8') as stream:
            self._content = json.load(stream)

    def dump(self) -> None:
        if not self._content:
            return
        with self.path.open(mode='w', encoding='utf8') as stream:
            json.dump(obj=self._content, fp=stream, indent=2, sort_keys=True)

    def add(self, func: str, contract: str, value: str) -> None:
        if contract != 'raises':
            raise ValueError('only raises contract is supported yet')

        contracts = self._content.setdefault(func, dict())
        values = contracts.setdefault(contract, [])
        if value not in values:
            values.append(value)
            values.sort()

    def get(self, func: str, contract: str) -> FrozenSet[str]:
        values = self._content.get(func, {}).get(contract, [])
        return frozenset(values)


class StubsManager:
    root = Path(__file__).parent / 'stubs'

    def __init__(self, paths: Sequence[Path] = None):
        self._modules = dict()
        if paths is None:
            self.paths = (self.root, )
        else:
            self.paths = tuple(paths)

    def read(self, path: Path) -> StubFile:
        if path.suffix == '.py':
            path = path.with_suffix(EXTENSION)
        if path.suffix != EXTENSION:
            raise ValueError('invalid stub file extension: *{}'.format(path.suffix))
        module_name = self._get_module_name(path=path)
        if module_name not in self._modules:
            stub = StubFile(path=path)
            stub.load()
            self._modules[module_name] = stub
        return self._modules[module_name]

    def _get_module_name(self, path: Path) -> str:
        # built-in stubs
        if path.parent == self.root:
            return path.stem
        # name is a full path to a module
        if '.' in path.stem:
            return path.stem
        # walk up by the tree as pytest does
        if not (path.parent / '__init__.py').exists():
            return path.stem
        for parent in path.parents:
            if not (parent / '__init__.py').exists():
                parts = path.relative_to(parent).with_suffix('').parts
                return '.'.join(parts)
        return path.stem

    def get(self, module_name: str) -> Optional[StubFile]:
        # cached
        stub = self._modules.get(module_name)
        if stub is not None:
            return stub
        # in the root
        for root in self.paths:
            path = root / (module_name + EXTENSION)
            if path.exists():
                return self.read(path)
        return None

    def create(self, path: Path) -> StubFile:
        if path.suffix == '.py':
            path = path.with_suffix(EXTENSION)
        if path.exists():
            return self.read(path=path)
        module_name = self._get_module_name(path=path)
        if module_name not in self._modules:
            stub = StubFile(path=path)
            self._modules[module_name] = stub
        return self._modules[module_name]


class PseudoFunc:
    __slots__ = ['name', 'body']

    def __init__(self, *, name: str, body):
        self.name = name
        self.body = body


def _get_funcs(*, path: Path) -> Iterator[PseudoFunc]:
    text = path.read_text()
    tree = astroid.parse(code=text, path=str(path))
    for expr in tree.body:
        # functions
        if type(expr) is astroid.FunctionDef:
            yield PseudoFunc(name=expr.name, body=expr.body)  # type: ignore

        # methods
        if type(expr) is astroid.ClassDef:
            for subexpr in expr.body:
                if type(subexpr) is not astroid.FunctionDef:
                    continue
                yield PseudoFunc(
                    name=expr.name + '.' + subexpr.name,
                    body=subexpr.body,
                )


def generate_stub(*, path: Path, stubs: StubsManager = None) -> Path:
    from ._extractors import get_exceptions

    if path.suffix != '.py':
        raise ValueError('invalid Python file extension: *{}'.format(path.suffix))

    if stubs is None:
        stubs = StubsManager()
    stub = stubs.create(path=path)
    for func in _get_funcs(path=path):
        for token in get_exceptions(body=func.body, stubs=stubs):
            value = token.value
            if isinstance(value, type):
                value = value.__name__
            stub.add(func=func.name, contract='raises', value=str(value))
    stub.dump()
    return stub.path
