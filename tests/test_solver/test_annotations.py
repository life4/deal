import pytest
from deal._solver._theorem import Conclusion
from .helpers import prove_f


@pytest.mark.parametrize('setup, ann, check', [
    ('', 'int', 'a - a == 0'),
    ('', 'float', 'a - a == 0'),
    # ('', 'str', 'len(a) >= 0 and a.startswith(a)'),
    ('', 'str', 'len(a) >= 0'),
    ('from typing import List', 'List[int]', 'len(a) >= 0'),
    ('from typing import List', 'List[int]', '(a != []) or (a == [])'),
    ('from typing import Set', 'Set[int]', '(a != set()) or (a == set())'),
])
def test_asserts_ok(setup: str, ann: str, check: str) -> None:
    text = """
        {s}
        def f(a: {a}):
            assert {c}
    """
    text = text.format(s=setup, a=ann, c=check)
    theorem = prove_f(text)
    assert theorem.conclusion is Conclusion.OK
