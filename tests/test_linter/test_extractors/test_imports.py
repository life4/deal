import ast

import astroid
import pytest

from deal.linter._extractors import get_imports


@pytest.mark.parametrize('text, expected', [
    ('from deal import pre', ('deal', )),
])
def test_get_imports_simple(text, expected):
    tree = astroid.parse(text)
    print(tree.repr_tree())
    returns = tuple(r.value for r in get_imports(body=tree.body))
    assert returns == expected

    tree = ast.parse(text)
    print(ast.dump(tree))
    returns = tuple(r.value for r in get_imports(body=tree.body))
    assert returns == expected
