import deal
from ._exec import exec, Stack, PushOp, AddOp


def test_exec():
    ops = Stack.make_empty()
    ops = ops.push(PushOp(10))
    assert exec(ops) == 10

    ops = Stack.make_empty()
    ops = ops.push(AddOp())
    ops = ops.push(PushOp(3))
    ops = ops.push(PushOp(4))
    assert exec(ops) == 3 + 4


def test_exec_prop():
    import hypothesis.strategies as st

    strategy = st.builds(
        Stack.from_list,
        st.lists(
            st.one_of(
                st.builds(PushOp, value=st.integers()),
                st.just(AddOp()),
            )
        ),
    )
    cases = deal.cases(
        func=exec,
        kwargs=dict(operations=strategy),
    )
    for case in cases:
        case()
