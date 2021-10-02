import ast
from types import MappingProxyType
from typing import Iterator, List, Type, TypeVar

from .._decorators import Has
from ._contract import Category, Contract
from ._error import Error
from ._extractors import (
    get_asserts, get_exceptions, get_imports, get_markers,
    get_pre, get_returns, get_value, has_returns,
)
from ._func import Func
from ._stub import StubsManager


T = TypeVar('T', bound=Type['Rule'])
rules: List['Rule'] = []


def register(rule: T) -> T:
    rules.append(rule())
    return rule


class Rule:
    __slots__ = ()
    code: int
    message: str


class ModuleRule(Rule):
    __slots__ = ()

    def __call__(self, tree: ast.Module) -> Iterator[Error]:
        raise NotImplementedError


class FuncRule(Rule):
    __slots__ = ()

    def __call__(self, func: Func, stubs: StubsManager = None) -> Iterator[Error]:
        raise NotImplementedError


@register
class CheckImports(ModuleRule):
    __slots__ = ()
    code = 1
    message = 'do not use `from deal import ...`, use `import deal` instead'

    def __call__(self, tree: ast.Module) -> Iterator[Error]:
        for token in get_imports(tree.body):
            if token.value != 'deal':
                continue
            yield Error(
                code=self.code,
                text=self.message,
                row=token.line,
                col=token.col,
            )


@register
class CheckPre(FuncRule):
    __slots__ = ()
    code = 11
    message = 'pre contract error'

    def __call__(self, func: Func, stubs: StubsManager = None) -> Iterator[Error]:
        # We test only contracted functions because of poor performance.
        # Inferring every called function in the whole project
        # is a really expensive operation.
        if not func.contracts:
            return
        context = func.contracts[0].context
        for token in get_pre(body=func.body, context=context):
            yield Error(
                code=self.code,
                text=token.marker or self.message,
                value=token.value,  # type: ignore
                row=token.line,
                col=token.col,
            )


@register
class CheckReturns(FuncRule):
    __slots__ = ()
    code = 12
    message = 'post contract error'

    def __call__(self, func: Func, stubs: StubsManager = None) -> Iterator[Error]:
        for contract in func.contracts:
            if contract.category != Category.POST:
                continue
            yield from self._check(func=func, contract=contract)

    def _check(self, func: Func, contract: Contract) -> Iterator[Error]:
        for token in get_returns(body=func.body):
            try:
                result = contract.run(token.value)
            except NameError:
                # cannot resolve contract dependencies
                return

            error_info = dict(
                row=token.line,
                col=token.col,
                code=self.code,
                value=str(token.value),
            )
            if isinstance(result, str):
                yield Error(text=result, **error_info)  # type: ignore
                continue
            if not result:
                yield Error(text=self.message, **error_info)  # type: ignore


@register
class CheckRaises(FuncRule):
    __slots__ = ()
    code = 21
    message = 'raises contract error'

    def __call__(self, func: Func, stubs: StubsManager = None) -> Iterator[Error]:
        cats = {Category.RAISES, Category.SAFE, Category.PURE}
        for contract in func.contracts:
            if contract.category not in cats:
                continue
            yield from self._check(func=func, contract=contract, stubs=stubs)

    def _check(self, func: Func, contract: Contract, stubs: StubsManager = None) -> Iterator[Error]:
        allowed = contract.exceptions
        allowed_types = tuple(exc for exc in allowed if type(exc) is not str)
        for token in get_exceptions(body=func.body, stubs=stubs):
            if token.value in allowed:
                continue
            exc = token.value
            if isinstance(exc, type):
                if issubclass(exc, allowed_types):
                    continue
                exc = exc.__name__
            yield Error(
                code=self.code,
                text=self.message,
                value=str(exc),
                row=token.line,
                col=token.col,
            )


@register
class CheckAsserts(FuncRule):
    __slots__ = ()
    code = 31
    message = 'assert error'

    def __call__(self, func: Func, stubs: StubsManager = None) -> Iterator[Error]:
        # do not validate asserts in tests
        if func.name.startswith('test_'):
            return
        for token in get_asserts(body=func.body):
            yield Error(
                code=self.code,
                text=self.message,
                value=str(token.value),
                row=token.line,
                col=token.col,
            )


@register
class CheckMarkers(FuncRule):
    __slots__ = ()
    code = 40
    message = 'missed marker'

    codes = MappingProxyType({
        'global': 41,
        'import': 42,
        'io': 43,
        'read': 44,
        'write': 45,
        'stdout': 46,
        'stderr': 47,
        'network': 48,
    })

    def __call__(self, func: Func, stubs: StubsManager = None) -> Iterator[Error]:
        for contract in func.contracts:
            markers = None
            if contract.category == Category.HAS:
                markers = [get_value(arg) for arg in contract.args]
            elif contract.category == Category.PURE:
                markers = []
            if markers is None:
                continue
            yield from self._check(func=func, has=Has(*markers))
            return

    @classmethod
    def _check(cls, func: Func, has: Has) -> Iterator[Error]:
        # function without IO must return something
        if not has.has_io and not has_returns(body=func.body):
            yield Error(
                code=cls.codes['io'],
                text=cls.message,
                value='io',
                row=func.line,
                col=func.col,
            )

        for token in get_markers(body=func.body):
            assert token.marker
            has_marker = getattr(has, 'has_{}'.format(token.marker), None)
            if has_marker is None:
                has_marker = token.marker in has.markers
            if has_marker:
                continue
            yield Error(
                code=cls.codes.get(token.marker, 40),
                text=cls.message,
                value=token.marker,
                row=token.line,
                col=token.col,
            )
