import deal


def inherit_method() -> None:
    class A:
        def f(self, x: int):
            raise NotImplementedError

    class B(A):
        @deal.inherit
        def f(self, x: int) -> float:
            raise NotImplementedError

    reveal_type(B().f)  # R: def (x: builtins.int) -> builtins.float


def inherit_class() -> None:
    class A:
        def f(self, x: int):
            raise NotImplementedError

    @deal.inherit
    class B(A):
        def f(self, x: int) -> float:
            raise NotImplementedError

    reveal_type(B().f)  # R: def (x: builtins.int) -> builtins.float
