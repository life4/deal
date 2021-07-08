import ast

import astroid
import pytest

from deal.linter._extractors import get_definitions


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
    tree = ast.parse(source)
    print(ast.dump(tree))
    defs = get_definitions(tree)
    assert set(defs) == names

    module = ast.parse('hello')
    for name, stmt in defs.items():
        module.body[0] = stmt
        print(name, '|>', ast.dump(module))
        compile(module, filename='<ast>', mode='exec')

    tree = astroid.parse(source)
    print(tree.repr_tree())
    defs = get_definitions(tree)
    assert set(defs) == names

    module = ast.parse('hello')
    for name, stmt in defs.items():
        module.body[0] = stmt
        print(name, '|>', ast.dump(module))
        compile(module, filename='<ast>', mode='exec')
