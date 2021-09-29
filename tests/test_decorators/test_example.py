import deal


def test_example_is_not_triggered_in_runtime():
    @deal.example(lambda: False)
    @deal.example(lambda: 1 / 0 == 0)
    def f1():
        return True

    assert f1() is True
