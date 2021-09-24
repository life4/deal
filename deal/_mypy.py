# This file is excluded from coverage.

import atexit
import os
from collections import defaultdict
from time import perf_counter
from typing import DefaultDict, List, Optional

from mypy import nodes
from mypy.checker import TypeChecker
from mypy.plugin import FunctionSigContext, Plugin
from mypy.types import AnyType, CallableType, TypeOfAny


perf: DefaultDict[str, List[float]] = defaultdict(list)
TRACK_PERF = os.getenv('DEAL_TRACK_PERF')


def show_perf():
    overall = .0
    for name, times in sorted(perf.items()):
        total = sum(times)
        count = len(times)
        mean = total / count
        print(f'{name:30} | {count:5} * {mean:.7f} = {total:.4f}')
        overall += total
    print(f'TOTAL: {overall}')


if TRACK_PERF:
    atexit.register(show_perf)


class DealMypyPlugin(Plugin):
    def __getattribute__(self, name: str):
        if not TRACK_PERF:
            return super().__getattribute__(name)

        start = perf_counter()
        try:
            return super().__getattribute__(name)
        finally:
            now = perf_counter()
            perf[name].append(now - start)

    def get_function_signature_hook(self, fullname: str):
        if fullname == 'deal._aliases.pre':
            return self._handle_pre
        if fullname == 'deal._aliases.post':
            return self._handle_post
        if fullname == 'deal._aliases.ensure':
            return self._handle_ensure
        if fullname == 'deal._aliases.reason':
            return self._handle_reason
        return None

    def _handle_reason(self, ctx: FunctionSigContext) -> CallableType:
        return self._handle_pre(ctx, position=1)

    def _handle_pre(self, ctx: FunctionSigContext, position: int = 0) -> CallableType:
        validator = ctx.args[position][0]
        if not isinstance(validator, nodes.LambdaExpr):
            return ctx.default_signature
        if validator.arg_names == ['_']:
            return ctx.default_signature
        dfn = self._get_parent(ctx)
        if dfn is None:
            return ctx.default_signature
        ftype = dfn.func.type
        assert isinstance(ftype, CallableType)
        return self._set_validator_type(
            ctx=ctx,
            ftype=ftype.copy_modified(ret_type=AnyType(TypeOfAny.explicit)),
            position=position,
        )

    def _handle_post(self, ctx: FunctionSigContext) -> CallableType:
        validator = ctx.args[0][0]
        if not isinstance(validator, nodes.LambdaExpr):
            return ctx.default_signature
        if validator.arg_names == ['_']:
            return ctx.default_signature
        dfn = self._get_parent(ctx)
        if dfn is None:
            return ctx.default_signature
        ftype = dfn.func.type
        assert isinstance(ftype, CallableType)
        return self._set_validator_type(ctx, CallableType(
            arg_types=[ftype.ret_type],
            arg_kinds=[nodes.ARG_POS],
            arg_names=[None],
            ret_type=AnyType(TypeOfAny.explicit),
            fallback=ftype.fallback,
        ))

    def _handle_ensure(self, ctx: FunctionSigContext) -> CallableType:
        if not isinstance(ctx.args[0][0], nodes.LambdaExpr):
            return ctx.default_signature
        if ctx.args[0][0].arg_names == ['_']:
            return ctx.default_signature
        dfn = self._get_parent(ctx)
        if dfn is None:
            return ctx.default_signature
        ftype = dfn.func.type
        assert isinstance(ftype, CallableType)
        return self._set_validator_type(ctx, CallableType(
            arg_types=ftype.arg_types + [ftype.ret_type],
            arg_kinds=ftype.arg_kinds + [nodes.ARG_POS],
            arg_names=ftype.arg_names + ['result'],
            ret_type=AnyType(TypeOfAny.explicit),
            fallback=ftype.fallback,
        ))

    @staticmethod
    def _set_validator_type(
        ctx: FunctionSigContext,
        ftype: CallableType,
        position: int = 0,
    ) -> CallableType:
        arg_types = ctx.default_signature.arg_types.copy()
        arg_types[position] = ftype
        return ctx.default_signature.copy_modified(arg_types=arg_types)

    def _get_parent(self, ctx: FunctionSigContext) -> Optional[nodes.Decorator]:
        checker = ctx.api
        assert isinstance(checker, TypeChecker)
        return self._find_func(defs=checker.tree.defs, target=ctx.context)

    def _find_func(self, defs: List[nodes.Statement], target: nodes.Context) -> Optional[nodes.Decorator]:
        for dfn in defs:
            if isinstance(dfn, nodes.Decorator):
                for dec in dfn.decorators:
                    if dec is target:
                        return dfn
                dfn = dfn.func
            if isinstance(dfn, nodes.FuncDef):
                result = self._find_func(defs=dfn.body.body, target=target)
                if result is not None:
                    return result
            if isinstance(dfn, nodes.ClassDef):
                result = self._find_func(defs=dfn.defs.body, target=target)
                if result is not None:
                    return result
        return None


def plugin(version: str):
    return DealMypyPlugin
