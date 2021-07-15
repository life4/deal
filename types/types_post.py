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
