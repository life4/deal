import deal


def preserve_function_annotation() -> None:
    @deal.pre(lambda a, b: a > b)
    def f(a: int, b: int) -> str:
        return str(a + b)
    reveal_type(f)  # R: def (a: builtins.int, b: builtins.int) -> builtins.str


def infer_validator_type() -> None:
    # E: "int" has no attribute "hi"
    @deal.pre(lambda a, b: a.hi)
    def f(a: int, b: int) -> bool:
        return a > b
