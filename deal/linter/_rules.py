# built-in
import ast
import enum
from typing import Iterator

# app
from ._contract import Category, Contract
from ._error import Error
from ._extractors import get_exceptions, get_imports, get_prints, get_returns, get_globals
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
class CheckReturns:
    code = 11
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
    code = 12
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
        for token in get_exceptions(body=func.body, stubs=stubs):
            if token.value in allowed:
                continue
            if issubclass(token.value, allowed_types):
                continue
            exc = token.value
            if not isinstance(exc, str):
                exc = exc.__name__
            yield Error(
                code=self.code,
                text=self.message,
                value=exc,
                row=token.line,
                col=token.col,
            )


@register
class CheckPrints:
    code = 13
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
    code = 14
    message = 'pure contract error'
    required = Required.FUNC

    def __call__(self, func: Func, stubs: StubsManager = None) -> Iterator[Error]:
        for contract in func.contracts:
            if contract.category != Category.PURE:
                continue
            yield from self._check(func=func)
            return

    def _check(self, func: Func, stubs: StubsManager = None) -> Iterator[Error]:
        for token in get_globals(body=func.body):
            yield Error(
                code=self.code,
                text=self.message,
                value=str(token.value),
                row=token.line,
                col=token.col,
            )
