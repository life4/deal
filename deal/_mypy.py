from mypy.plugin import FunctionSigContext, Plugin
from mypy.types import CallableType, AnyType, TypeOfAny
from mypy.nodes import ARG_POS, Decorator, LambdaExpr, MypyFile, Context
from mypy.checker import TypeChecker


class DealMypyPlugin(Plugin):
    def get_function_signature_hook(self, fullname: str):
        if fullname == 'deal._aliases.post':
            return self._handle_post
        return None

    def _handle_post(self, ctx: FunctionSigContext) -> CallableType:
        if not isinstance(ctx.args[0][0], LambdaExpr):
            return ctx.default_signature
        checker = ctx.api
        assert isinstance(checker, TypeChecker)
        dfn = self._get_def(checker.tree, ctx.context)
        ftype = dfn.func.type
        assert isinstance(ftype, CallableType)
        validator_type = CallableType(
            arg_types=[ftype.ret_type],
            arg_kinds=[ARG_POS],
            arg_names=ctx.args[0][0].arg_names,
            ret_type=AnyType(TypeOfAny.explicit),
            fallback=ftype.fallback,
        )
        dec_sig = ctx.default_signature.copy_modified()
        dec_sig.arg_types[0] = validator_type
        return dec_sig

    @staticmethod
    def _get_def(tree: MypyFile, target: Context) -> Decorator:
        for dfn in tree.defs:
            if not isinstance(dfn, Decorator):
                continue
            for dec in dfn.decorators:
                if dec is target:
                    return dfn
        raise ValueError('{} not found'.format(target))


def plugin(version: str):
    return DealMypyPlugin
