# built-in
import typing

# external
import astroid
import z3

# app
from ..linter._extractors.contracts import get_contracts
from ._context import Context, Scope
from ._eval_expr import eval_expr
from ._exceptions import UnsupportedError


def eval_contracts(decorators: astroid.Decorators, ctx: Context) -> typing.Dict[str, z3.Goal]:
    goals = dict(
        pre=z3.Goal(),
        post=z3.Goal(),
    )
    if not decorators:
        return goals
    return_value = ctx.scope.get('return')
    for contract_name, args in get_contracts(decorators.nodes):
        if contract_name not in {'pre', 'post'}:
            continue
        if contract_name == 'post' and return_value is None:
            raise UnsupportedError('cannot resolve return value to check deal.post')
        contract = args[0]
        if not isinstance(contract, astroid.Lambda):
            continue
        if not contract.args:
            continue

        # make context
        cargs = contract.args.arguments
        contract_context = ctx
        if contract_name == 'post':
            assert return_value is not None
            # check post-condition in a new clear scope
            # with mapping `return` value in it as an argument.
            contract_context = contract_context.evolve(scope=Scope.make_empty())
            contract_context.scope.set(
                name=cargs[0].name,
                value=return_value,
            )

        # eval contract
        value = eval_expr(node=contract.body, ctx=contract_context)
        goals[contract_name].add(value)
    return goals
