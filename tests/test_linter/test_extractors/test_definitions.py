import ast

import pytest

from deal.linter._extractors import get_definitions


try:
    import astroid
except ImportError:
    astroid = None


@pytest.mark.parametrize('source, names', [
    ('import re', {'re'}),
    ('import typing, types', {'typing', 'types'}),
    ('import typing as types', {'types'}),
    ('from . import hi', set()),
    ('from .something import hi', set()),

    ('from typing import List', {'List'}),
    ('from typing import List, Dict', {'List', 'Dict'}),

    ('ab = 2', {'ab'}),
    ('ab = cd = 23', {'ab', 'cd'}),
    ('ab.cd = 2', set()),
])
def test_extract_defs(source: str, names) -> None:
    ast_tree = ast.parse(source)
    print(ast.dump(ast_tree))
    ast_defs = get_definitions(ast_tree)
    assert set(ast_defs) == names

    if astroid is not None:
        tree = astroid.parse(source)
        print(tree.repr_tree())
        defs = get_definitions(tree)
        assert set(defs) == names
