from __future__ import annotations

import ast
from textwrap import dedent
from typing import TypeVar

from deal.linter._func import Func


T = TypeVar('T')


def first(funcs: list[T]) -> T:
    assert len(funcs) == 1
    return funcs[0]


def funcs_from_ast(text: str) -> list[Func]:
    text = dedent(text).strip()
    tree = ast.parse(text)
    print(ast.dump(tree))
    return Func.from_ast(tree)


def funcs_from_astroid(text: str) -> list[Func]:
    import astroid

    text = dedent(text).strip()
    tree = astroid.parse(text)
    print(tree.repr_tree())
    return Func.from_astroid(tree)
