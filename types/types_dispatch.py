import deal


def preserve_function_annotation() -> None:
    @deal.dispatch
    def double(a: int) -> int:
        raise NotImplementedError

    @double.register
    @deal.pre(lambda a: a == 2)
    def _1(a: int) -> int:
        return 4

    # Preserve function type
    # R: deal._runtime._dispatch.Dispatch[def (a: builtins.int) -> builtins.int]
    reveal_type(double)

    res = double(2)
    reveal_type(res)  # R: builtins.int

    # Enforce contrvariance
    # E: Argument 1 to "register" of "Dispatch" has incompatible type "Callable[[bool], int]"; expected "Callable[[int], int]"
    @double.register
    def _2(a: bool) -> int:
        return 4

    # Enforce covariance
    # E: Argument 1 to "register" of "Dispatch" has incompatible type "Callable[[int], float]"; expected "Callable[[int], int]"
    @double.register
    def _3(a: int) -> float:
        return True
