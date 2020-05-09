# built-in
import ast
import enum
from itertools import chain
from typing import Iterator

# app
from ._contract import Category, Contract
from ._error import Error
from ._extractors import (
    get_asserts, get_exceptions, get_exceptions_stubs, get_globals,
    get_imports, get_pre, get_prints, get_returns, has_returns,
)
from ._func import Func
from ._stub import StubsManager


rules = []


class Required(enum.Enum):
    FUNC = 'func'
    MODULE = 'module'


def register(rule):
    rules.append(rule())
    return rule


@register
class CheckImports:
    __slots__ = ()
    code = 1
    message = 'do not use `from deal import ...`, use `import deal` instead'
    required = Required.MODULE

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
class CheckPre:
    __slots__ = ()
    code = 11
    message = 'pre contract error'
    required = Required.FUNC

    def __call__(self, func: Func, stubs: StubsManager = None) -> Iterator[Error]:
        for token in get_pre(body=func.body):
            yield Error(
                code=self.code,
                text=self.message,
                value=token.value,  # type: ignore
                row=token.line,
                col=token.col,
            )


@register
class CheckReturns:
    __slots__ = ()
    code = 12
    message = 'post contract error'
    required = Required.FUNC

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
class CheckRaises:
    __slots__ = ()
    code = 21
    message = 'raises contract error'
    required = Required.FUNC

    def __call__(self, func: Func, stubs: StubsManager = None) -> Iterator[Error]:
        for contract in func.contracts:
            if contract.category != Category.RAISES:
                continue
            yield from self._check(func=func, contract=contract, stubs=stubs)

    def _check(self, func: Func, contract: Contract, stubs: StubsManager = None) -> Iterator[Error]:
        allowed = contract.exceptions
        allowed_types = tuple(exc for exc in allowed if type(exc) is not str)
        tokens = [get_exceptions(body=func.body)]
        if stubs is not None:
            tokens.append(get_exceptions_stubs(body=func.body, stubs=stubs))
        for token in chain(*tokens):
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
class CheckPrints:
    __slots__ = ()
    code = 22
    message = 'silent contract error'
    required = Required.FUNC

    def __call__(self, func: Func, stubs: StubsManager = None) -> Iterator[Error]:
        for contract in func.contracts:
            if contract.category != Category.SILENT:
                continue
            yield from self._check(func=func)
            # if `@deal.silent` is duplicated, check the function only once
            return

    def _check(self, func: Func, stubs: StubsManager = None) -> Iterator[Error]:
        for token in get_prints(body=func.body):
            yield Error(
                code=self.code,
                text=self.message,
                value=str(token.value),
                row=token.line,
                col=token.col,
            )


@register
class CheckPure:
    __slots__ = ()
    code = 23
    message = 'pure contract error'
    required = Required.FUNC

    def __call__(self, func: Func, stubs: StubsManager = None) -> Iterator[Error]:
        for contract in func.contracts:
            if contract.category != Category.PURE:
                continue
            yield from self._check(func=func)
            return

    def _check(self, func: Func, stubs: StubsManager = None) -> Iterator[Error]:
        if not has_returns(body=func.body):
            yield Error(
                code=self.code,
                text=self.message,
                value='no return',
                row=func.line,
                col=func.col,
            )
        for token in get_globals(body=func.body):
            yield Error(
                code=self.code,
                text=self.message,
                value=str(token.value),
                row=token.line,
                col=token.col,
            )


@register
class CheckAsserts:
    __slots__ = ()
    code = 31
    message = 'assert error'
    required = Required.FUNC

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
