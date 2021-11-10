import pytest

import deal


def test_inherit_one_parent():
    class A:
        @deal.pre(lambda self, x: x == 3)
        def f(self, x):
            raise NotImplementedError

    class B(A):
        @deal.inherit
        def f(self, x):
            return x * 2

    b = B()
    assert b.f(3) == 6
    with pytest.raises(deal.PreContractError):
        b.f(4)


def test_inherit_no_parents():
    class A:
        @deal.inherit
        def f(self, x):
            return x * 2

    a = A()
    assert a.f(3) == 6
    assert a.f(4) == 8


def test_inherit_function():
    @deal.inherit
    def f(x):
        return x * 2

    assert f(3) == 6
    assert f(4) == 8


def test_inherit_one_parent_no_contracts():
    class A:
        def f(self, x):
            raise NotImplementedError

    class B(A):
        @deal.inherit
        def f(self, x):
            return x * 2

    b = B()
    assert b.f(3) == 6
    assert b.f(4) == 8


def test_inherit_multiple_parents():
    class A:
        def f(self, x):
            raise NotImplementedError

    class B:
        @deal.pre(lambda self, x: x > 0)
        def f(self, x):
            raise NotImplementedError

    class C(B):
        @deal.pre(lambda self, x: x < 5)
        def f(self, x):
            raise NotImplementedError

    class D(C, A):
        @deal.inherit
        def f(self, x):
            return x * 2

    d = D()
    assert d.f(3) == 6
    with pytest.raises(deal.PreContractError):
        assert d.f(-2) == -4
    with pytest.raises(deal.PreContractError):
        d.f(8)


def test_inherit_one_parent__preserve_contracts():
    class A:
        @deal.pre(lambda self, x: x < 5)
        def f(self, x):
            raise NotImplementedError

    class B(A):
        @deal.inherit
        @deal.pre(lambda self, x: x > 0)
        def f(self, x):
            return x * 2

    b = B()
    assert b.f(3) == 6
    with pytest.raises(deal.PreContractError):
        b.f(6)
    with pytest.raises(deal.PreContractError):
        b.f(-2)


def test_inherit_class():
    class A:
        @deal.pre(lambda self, x: x == 3)
        def f(self, x):
            raise NotImplementedError

    @deal.inherit
    class B(A):
        def f(self, x):
            return x * 2

    b = B()
    assert b.f(3) == 6
    with pytest.raises(deal.PreContractError):
        b.f(4)


def test_inherit_inherit():
    class A:
        @deal.inherit
        @deal.pre(lambda self, x: x == 3)
        def f(self, x):
            pass

    class B(A):
        @deal.inherit
        def f(self, x):
            return x * 2

    b = B()
    assert b.f(3) == 6
    with pytest.raises(deal.PreContractError):
        b.f(4)


def test_has_inherit():
    class A:
        @deal.has('a', 'b')
        def f(self, x):
            raise NotImplementedError

    @deal.inherit
    class B(A):
        def f(self, x):
            return x * 2

    b = B()
    contract = next(deal.introspection.get_contracts(b.f))
    assert isinstance(contract, deal.introspection.Has)
    assert contract.markers == frozenset({'a', 'b'})


def test_has_inherit_and_merge():
    class A:
        @deal.has('a', 'b')
        def f(self, x):
            raise NotImplementedError

    @deal.inherit
    class B(A):
        @deal.has('c', 'd')
        def f(self, x):
            return x * 2

    b = B()
    contract = next(deal.introspection.get_contracts(b.f))
    assert isinstance(contract, deal.introspection.Has)
    assert contract.markers == frozenset({'a', 'b', 'c', 'd'})


def test_has_preserve():
    class A:
        def f(self, x):
            raise NotImplementedError

    @deal.inherit
    class B(A):
        @deal.has('a', 'b')
        def f(self, x):
            return x * 2

    b = B()
    contract = next(deal.introspection.get_contracts(b.f))
    assert isinstance(contract, deal.introspection.Has)
    assert contract.markers == frozenset({'a', 'b'})
