import deal


def inherit_method() -> None:
    class A:
        def f(self, x: int):
            pass

    class B(A):
        @deal.inherit
        def f(self, x: int) -> float:
            pass

    reveal_type(B().f)  # R: def (x: builtins.int) -> builtins.float


def inherit_class() -> None:
    class A:
        def f(self, x: int):
            pass

    @deal.inherit
    class B(A):
        def f(self, x: int) -> float:
            pass

    reveal_type(B().f)  # R: def (x: builtins.int) -> builtins.float
