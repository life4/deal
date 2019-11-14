import deal
import pytest


def test_setting_object_attribute_fulfills_contract():
    @deal.inv(lambda obj: obj.x > 0)
    class A:
        x = 2

    a = A()
    a.x = 4
    with pytest.raises(deal.InvContractError):
        a.x = -2


def test_setting_wrong_args_by_method_raises_error():
    @deal.inv(lambda obj: obj.x > 0)
    class A:
        x = 2

        def f(self, x):
            self.x = x

    a = A()

    a.f(4)
    with pytest.raises(deal.InvContractError):
        a.f(-2)


def test_chain_contracts_both_fulfill():
    @deal.inv(lambda obj: obj.x > 0)
    @deal.inv(lambda obj: obj.x < 10)
    class A:
        x = 2

    a = A()
    a.x = 4
    with pytest.raises(deal.InvContractError):
        a.x = -2
    with pytest.raises(deal.InvContractError):
        a.x = 20


def test_patched_invariants_instance():
    class A:
        x = 2

    PatchedA = deal.inv(lambda obj: obj.x > 0)(A)  # noQA
    a = PatchedA()
    assert isinstance(a, PatchedA)
    assert isinstance(a, A)

    PatchedA2 = deal.inv(lambda obj: obj.x > 0)(PatchedA)  # noQA
    a = PatchedA2()
    assert isinstance(a, PatchedA)
    assert isinstance(a, PatchedA2)
    assert isinstance(a, A)

    assert a.__class__.__name__.count('Invarianted') == 1
