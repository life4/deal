# built-in
import typing

# external
import astroid


if typing.TYPE_CHECKING:
    # app
    from .._context import Context


class LambdaSort(typing.NamedTuple):
    ctx: 'Context'
    args: astroid.Arguments
    body: astroid.Expr

    def __call__(self, *values, **kwargs):
        # app
        from .._eval_expr import eval_expr

        body_ctx = self.ctx.make_child()
        for arg, value in zip(self.args.arguments, values):
            body_ctx.scope.set(name=arg.name, value=value)
        return eval_expr(node=self.body, ctx=body_ctx)
