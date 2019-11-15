import ast

import astroid

from deal.linter._contract import Contract, Category
from deal.linter._func import Func

TEXT = """
import deal

@deal.raises(ValueError, UnknownError, idk_what_is_it())
@notadeal.raises(KeyError)
def f(x):
    return x
"""


def test_exceptions():
    funcs1 = Func.from_ast(ast.parse(TEXT))
    assert len(funcs1) == 1
    funcs2 = Func.from_astroid(astroid.parse(TEXT))
    assert len(funcs2) == 1
    for func in (funcs1[0], funcs2[0]):
        assert len(func.contracts) == 1
        contract = func.contracts[0]
        assert contract.exceptions == [ValueError, 'UnknownError']


def test_repr():
    c = Contract(category=Category.RAISES, args=[])
    assert repr(c) == 'Contract(raises)'
