import ast
from types import MappingProxyType
from typing import Iterator, List, Optional, Set, Type, TypeVar, Union

import astroid

from .._runtime import HasPatcher
from ._contract import Category, Contract
from ._error import Error
from ._extractors import (
    UNKNOWN, get_asserts, get_example, get_exceptions, get_imports,
    get_markers, get_pre, get_returns, get_value, has_returns, uses_result,
)
from ._func import Func
from ._stub import StubsManager


T = TypeVar('T', bound=Type['Rule'])
Exceptions = List[Union[str, Type[Exception]]]
rules: List['Rule'] = []


def register(rule: T) -> T:
    rules.append(rule())
    return rule


class Rule:
    __slots__ = ()
    code: int
    message: str

    def _validate(self, contract: Contract, args, kwargs, **error_info) -> Optional[Error]:
        try:
            result = contract.run(*args, **kwargs)
        except NameError:
            # cannot resolve contract dependencies
            return None
        if isinstance(result, str):
            return Error(text=result, code=self.code, **error_info)
        if not result:
            return Error(text=self.message, code=self.code, **error_info)
        return None


class ModuleRule(Rule):
    __slots__ = ()

    def __call__(self, tree: ast.Module) -> Iterator[Error]:
        raise NotImplementedError


class FuncRule(Rule):
    __slots__ = ()

    def __call__(self, func: Func, stubs: Optional[StubsManager] = None) -> Iterator[Error]:
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
class CheckEnsureArgs(FuncRule):
    __slots__ = ()
    code = 2
    message = 'ensure contract must have `result` arg'

    def __call__(self, func: Func, stubs: Optional[StubsManager] = None) -> Iterator[Error]:
        for contract in func.contracts:
            if contract.category != Category.ENSURE:
                continue
            yield from self._check(contract)

    def _check(self, contract: Contract) -> Iterator[Error]:
        validator = contract.args[0]
        if not uses_result(validator):
            yield Error(
                code=self.code,
                text=self.message,
                row=validator.lineno,
                col=validator.col_offset,
            )


@register
class CheckPre(FuncRule):
    __slots__ = ()
    code = 11
    message = 'pre contract error'

    def __call__(self, func: Func, stubs: Optional[StubsManager] = None) -> Iterator[Error]:
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

    def __call__(self, func: Func, stubs: Optional[StubsManager] = None) -> Iterator[Error]:
        for contract in func.contracts:
            if contract.category != Category.POST:
                continue
            yield from self._check(func=func, contract=contract)

    def _check(self, func: Func, contract: Contract) -> Iterator[Error]:
        for token in get_returns(body=func.body):
            error = self._validate(
                contract=contract,
                args=(token.value,),
                kwargs={},
                row=token.line,
                col=token.col,
                value=str(token.value),
            )
            if error is not None:
                yield error


@register
class CheckExamples(FuncRule):
    __slots__ = ()
    code = 13
    message = 'example violates contract'

    def __call__(self, func: Func, stubs: Optional[StubsManager] = None) -> Iterator[Error]:
        for contract in func.contracts:
            if contract.category != Category.EXAMPLE:
                continue
            yield from self._check(func=func, contract=contract)

    def _check(self, func: Func, contract: Contract) -> Iterator[Error]:
        token = contract.args[0]
        if not isinstance(token, (ast.Lambda, astroid.Lambda)):
            return
        example = get_example(token.body, func_name=func.name)
        if example is None:
            return
        for other in func.contracts:
            if other.category == Category.PRE:
                error = self._validate(
                    contract=other,
                    args=example.args,
                    kwargs=example.kwargs,
                    row=token.lineno,
                    col=token.col_offset,
                    value='deal.pre',
                )
                if error is not None:
                    yield error

            if other.category == Category.POST:
                if example.result == UNKNOWN:
                    continue
                error = self._validate(
                    contract=other,
                    args=(example.result, ),
                    kwargs={},
                    row=token.lineno,
                    col=token.col_offset,
                    value='deal.post',
                )
                if error is not None:
                    yield error

            if other.category == Category.ENSURE:
                if example.result == UNKNOWN:
                    continue
                error = self._validate(
                    contract=other,
                    args=example.args,
                    kwargs=dict(example.kwargs, result=example.result),
                    row=token.lineno,
                    col=token.col_offset,
                    value='deal.ensure',
                )
                if error is not None:
                    yield error


@register
class CheckRaises(FuncRule):
    __slots__ = ()
    code = 21
    message = 'raises contract error'

    def __call__(self, func: Func, stubs: Optional[StubsManager] = None) -> Iterator[Error]:
        cats = {Category.RAISES, Category.SAFE, Category.PURE}
        declared: Exceptions = [AssertionError]
        check = False
        for contract in func.contracts:
            if contract.category not in cats:
                continue
            declared.extend(contract.exceptions)
            check = True
        if check:
            yield from self.get_undeclared(func, declared, stubs)

    def get_undeclared(
        self,
        func: Func,
        declared: Exceptions,
        stubs: Optional[StubsManager] = None,
    ) -> Iterator[Error]:
        declared_types = tuple(exc for exc in declared if not isinstance(exc, str))
        for token in get_exceptions(body=func.body, stubs=stubs):
            if token.value in declared:
                continue
            exc = token.value
            if isinstance(exc, type):
                if issubclass(exc, declared_types):
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

    def __call__(self, func: Func, stubs: Optional[StubsManager] = None) -> Iterator[Error]:
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
        'stdin': 49,
        'syscall': 50,

        'random': 55,
        'time': 56,
    })

    def __call__(self, func: Func, stubs: Optional[StubsManager] = None) -> Iterator[Error]:
        for contract in func.contracts:
            markers: Optional[Set[str]] = None
            if contract.category == Category.HAS:
                markers = set()
                for arg in contract.args:
                    value = get_value(arg)
                    if isinstance(value, str):
                        markers.add(value)
            elif contract.category == Category.PURE:
                markers = set()
            if markers is None:  # this is needed to fix coverage quirks
                continue
            yield from self.get_undeclared(func=func, markers=markers)
            return

    @classmethod
    def get_undeclared(cls, func: Func, markers: Set[str]) -> Iterator[Error]:
        has = HasPatcher(markers)
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
            has_marker = getattr(has, f'has_{token.marker}', None)
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
