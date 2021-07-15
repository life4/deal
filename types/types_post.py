import deal


def preserve_function_annotation() -> None:
    @deal.post(lambda r: r > 0)
    def f() -> int:
        return 4
    reveal_type(f())  # R: builtins.int


def infer_validator_type() -> None:
    # E: "int" has no attribute "hi"
    @deal.post(lambda r: r.hi)
    def f() -> int:
        return 4


def report_bad_arity() -> None:
    # TODO: Fix "Cannot infer type of lambda"

    # E: Argument 1 to "post" has incompatible type "Callable[[], bool]"; expected "Callable[[int], Any]"
    @deal.post(lambda: True)  # E: Cannot infer type of lambda
    def f() -> int:
        return 4
