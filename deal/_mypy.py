from typing import List, Optional
from mypy.plugin import FunctionSigContext, Plugin
from mypy.types import CallableType, AnyType, TypeOfAny
from mypy import nodes
from mypy.checker import TypeChecker


class DealMypyPlugin(Plugin):
    def get_function_signature_hook(self, fullname: str):
        if fullname == 'deal._aliases.post':
            return self._handle_post
        return None

    def _handle_post(self, ctx: FunctionSigContext) -> CallableType:
        if not isinstance(ctx.args[0][0], nodes.LambdaExpr):
            return ctx.default_signature
        dfn = self._get_parent(ctx)
        if dfn is None:
            raise ValueError('not found')
        ftype = dfn.func.type
        assert isinstance(ftype, CallableType)
        names = ctx.args[0][0].arg_names
        if len(names) != 1:
            names = ['result']
        validator_type = CallableType(
            arg_types=[ftype.ret_type],
            arg_kinds=[nodes.ARG_POS],
            arg_names=names,
            ret_type=AnyType(TypeOfAny.explicit),
            fallback=ftype.fallback,
        )
        dec_sig = ctx.default_signature.copy_modified()
        dec_sig.arg_types[0] = validator_type
        return dec_sig

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
        return None


def plugin(version: str):
    return DealMypyPlugin
