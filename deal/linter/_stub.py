import json
from pathlib import Path
from typing import Any, Dict, FrozenSet, Iterator, NamedTuple, Optional, Sequence, Tuple

import astroid

from ._contract import Category


EXTENSION = '.json'
ROOT = Path(__file__).parent / 'stubs'
CPYTHON_ROOT = ROOT / 'cpython'


class StubFile:
    __slots__ = ('path', '_content')
    path: Path
    _content: Dict[str, Dict[str, Any]]

    def __init__(self, path: Path) -> None:
        self.path = path
        self._content = dict()

    def load(self) -> None:
        with self.path.open(encoding='utf8') as stream:
            self._content = json.load(stream)

    def dump(self) -> None:
        if not self._content:
            return
        with self.path.open(mode='w', encoding='utf8') as stream:
            json.dump(obj=self._content, fp=stream, indent=2, sort_keys=True)

    def add(self, func: str, contract: Category, value: str) -> None:
        if contract not in (Category.RAISES, Category.HAS):
            raise ValueError('unsupported contract')
        contracts = self._content.setdefault(func, dict())
        values = contracts.setdefault(contract.value, [])
        if value in values:
            return
        values.append(value)
        values.sort()

    def get(self, func: str, contract: Category) -> FrozenSet[str]:
        if contract not in (Category.RAISES, Category.HAS):
            raise ValueError('unsupported contract')
        values = self._content.get(func, {}).get(contract.value, [])
        return frozenset(values)


class StubsManager:
    __slots__ = ('paths', '_modules')
    _modules: Dict[str, StubFile]
    paths: Tuple[Path, ...]

    default_paths = (ROOT, CPYTHON_ROOT)

    def __init__(self, paths: Optional[Sequence[Path]] = None) -> None:
        self._modules = dict()
        if paths is None:
            self.paths = self.default_paths
        else:
            self.paths = tuple(paths)

    def read(self, *, path: Path, module_name: Optional[str] = None) -> StubFile:
        if path.suffix == '.py':
            path = path.with_suffix(EXTENSION)
        if path.suffix != EXTENSION:
            raise ValueError(f'invalid stub file extension: *{path.suffix}')
        if module_name is None:
            module_name = self._get_module_name(path=path)
        if module_name not in self._modules:
            stub = StubFile(path=path)
            stub.load()
            self._modules[module_name] = stub
        return self._modules[module_name]

    @staticmethod
    def _get_module_name(path: Path) -> str:
        path = path.resolve()
        # walk up by the tree as pytest does
        if not (path.parent / '__init__.py').exists():
            return path.stem
        for parent in path.parents:
            if not (parent / '__init__.py').exists():
                parts = path.relative_to(parent).with_suffix('').parts
                return '.'.join(parts)
        raise RuntimeError('unreachable: __init__.py files up to root?')  # pragma: no cover

    def get(self, module_name: str) -> Optional[StubFile]:
        # cached
        stub = self._modules.get(module_name)
        if stub is not None:
            return stub
        # in the root
        for root in self.paths:
            path = root / (module_name + EXTENSION)
            if path.exists():
                return self.read(path=path, module_name=module_name)
            path = root.joinpath(*module_name.split('.')).with_suffix(EXTENSION)
            if path.exists():
                return self.read(path=path, module_name=module_name)
        return None

    def create(self, path: Path) -> StubFile:
        if path.suffix == '.py':
            path = path.with_suffix(EXTENSION)
        module_name = self._get_module_name(path=path)

        # if the stub for file is somewhere in the paths, use this instead.
        stub = self.get(module_name=module_name)
        if stub is not None:
            return stub

        # create new stub and load it from disk if the file exists
        stub = StubFile(path=path)
        if path.exists():
            stub.load()
        self._modules[module_name] = stub
        return stub


class PseudoFunc(NamedTuple):
    name: str
    body: list


def _get_funcs(*, path: Path) -> Iterator[PseudoFunc]:
    text = path.read_text()
    tree = astroid.parse(code=text, path=str(path))
    for expr in tree.body:
        yield from _get_funcs_from_expr(expr=expr)


def _get_funcs_from_expr(expr, prefix: str = '') -> Iterator[PseudoFunc]:
    name = getattr(expr, 'name', '')
    if prefix:
        name = prefix + '.' + name

    # functions
    if type(expr) is astroid.FunctionDef:
        yield PseudoFunc(name=name, body=expr.body)
    if type(expr) is astroid.AsyncFunctionDef:
        yield PseudoFunc(name=name, body=expr.body)

    # methods
    if type(expr) is astroid.ClassDef:
        for subexpr in expr.body:
            yield from _get_funcs_from_expr(expr=subexpr, prefix=name)


def generate_stub(*, path: Path, stubs: Optional[StubsManager] = None) -> Path:
    from ._extractors import get_exceptions, get_markers

    if path.suffix != '.py':
        raise ValueError(f'invalid Python file extension: *{path.suffix}')

    if stubs is None:
        stubs = StubsManager()
    stub = stubs.create(path=path)
    for func in _get_funcs(path=path):
        for token in get_exceptions(body=func.body, stubs=stubs):
            value = token.value
            if isinstance(value, type):
                value = value.__name__
            stub.add(func=func.name, contract=Category.RAISES, value=str(value))
        for token in get_markers(body=func.body, stubs=stubs):
            assert token.marker is not None
            stub.add(func=func.name, contract=Category.HAS, value=token.marker)
    stub.dump()
    return stub.path
