import ast

import pytest

from deal.linter._extractors import uses_result


try:
    import astroid
except ImportError:
    astroid = None


@pytest.mark.parametrize('given, expected', [
    # positive
    ('lambda a, result: 0', True),
    ('lambda a, result: 0', True),
    ('lambda a, *, result: 0', True),
    ('lambda *a, result: 0', True),
    ('lambda *a, result=None: 0', True),
    ('lambda _: _.result', True),
    ('lambda _: len(_.result) == _.length', True),

    # non-lambdas are allowed
    ('unknown', True),
    ('sum', True),

    # negative
    ('lambda _: 0', False),
    ('lambda _: _', False),
    ('lambda _: _.other', False),
    ('lambda a: 0', False),
    ('lambda a, res: 0', False),
    ('lambda a, *, res: 0', False),
])
def test_uses_result(given: str, expected: bool):
    if astroid is not None:
        tree = astroid.parse(given)
        print(tree.repr_tree())
        validator = tree.body[0].value
        assert uses_result(validator) is expected

    ast_tree = ast.parse(given)
    print(ast.dump(ast_tree))
    validator = ast_tree.body[0].value  # type: ignore[attr-defined]
    assert uses_result(validator) is expected
