from deal._mem_test import MemoryTracker


def test_mem_dump_no_diff():
    def f() -> int:
        return 123

    tracker = MemoryTracker()
    with tracker:
        f()
    assert not tracker.diff


def test_mem_dump_ignore_locals():
    def f():
        a = 456
        b = a
        return b

    tracker = MemoryTracker()
    with tracker:
        f()
    assert not tracker.diff


def test_mem_dump_side_effect():
    a = []

    def f() -> int:
        a.append({12})
        return 123

    tracker = MemoryTracker()
    with tracker:
        f()
    assert dict(tracker.diff) == {'set': 1}
