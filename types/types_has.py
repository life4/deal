import deal


def preserve_function_annotation() -> None:
    @deal.has('db', 'network')
    def f(a: int, b: int) -> str:
        return str(a + b)
    reveal_type(f)  # R: def (a: builtins.int, b: builtins.int) -> builtins.str
