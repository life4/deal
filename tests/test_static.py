

from deal.linter._func import Func


TEXT = """
import deal

@deal.post(lambda x: x > 0)
def f(x):
    return x
"""


def test_func():
    funcs = Func.from_text(TEXT)
    assert len(funcs) == 1
    func = funcs[0]
    assert func.run(1) is True
    assert func.run(-1) is False
