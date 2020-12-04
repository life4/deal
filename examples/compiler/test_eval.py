import deal
from ._eval import eval, IntNode, AddNode


def test_eval():
    assert eval(IntNode(4)) == 4

    node = AddNode(IntNode(2), IntNode(3))
    assert eval(node) == 2 + 3

    node = AddNode(IntNode(3), IntNode(4))
    node = AddNode(IntNode(2), node)
    assert eval(node) == 2 + 3 + 4


def test_eval_prop():
    import hypothesis.strategies as st

    strategy = st.one_of(
        st.builds(IntNode, st.integers()),
        st.deferred(lambda: st.builds(AddNode, strategy, strategy)),
    )
    cases = deal.cases(
        func=eval,
        kwargs=dict(node=strategy),
    )
    for case in cases:
        case()
