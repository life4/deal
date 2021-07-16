import deal


def preserve_function_annotation() -> None:
    @deal.ensure(lambda a, b, result: a > b)
    def f(a: int, b: int) -> str:
        return str(a + b)
    reveal_type(f)  # R: def (a: builtins.int, b: builtins.int) -> builtins.str


def infer_validator_type() -> None:
    # E: "int" has no attribute "hi"
    @deal.ensure(lambda a, b, result: a.hi)
    # E: "str" has no attribute "hello"
    @deal.ensure(lambda a, b, result: result.hello)
    def f(a: int, b: int) -> str:
        return str(a + b)
