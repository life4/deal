import ast

import pytest

from deal.linter._extractors import get_imports


try:
    import astroid
except ImportError:
    astroid = None


@pytest.mark.parametrize('text, expected', [
    ('from deal import pre', ('deal', )),
])
def test_get_imports_simple(text, expected):
    if astroid is not None:
        tree = astroid.parse(text)
        print(tree.repr_tree())
        returns = tuple(r.value for r in get_imports(body=tree.body))
        assert returns == expected

    ast_tree = ast.parse(text)
    print(ast.dump(ast_tree))
    returns = tuple(r.value for r in get_imports(body=ast_tree.body))
    assert returns == expected
