import deal


def preserve_function_annotation() -> None:
    @deal.post(lambda r: r > 0)
    def f() -> int:
        return 4
    reveal_type(f)  # R: def () -> builtins.int


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


def detect_methods() -> None:
    class A:
        # E: "int" has no attribute "hi"
        @deal.post(lambda r: r.hi)
        def f(self) -> int:
            return 4


def do_not_fail_on_vaa_simple() -> None:
    @deal.post(lambda _: _.result == 4)
    def f(self) -> int:
        return 4
