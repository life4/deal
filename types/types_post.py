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

    # E: Argument 1 to "post" has incompatible type "Callable[[], bool]"; expected "Callable[[int], Union[bool, str]]"
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


def report_bad_return_type() -> None:
    # E: Argument 1 to "post" has incompatible type "Callable[[int], int]"; expected "Callable[[int], Union[bool, str]]"
    @deal.post(lambda x: x)  # E: Incompatible return value type (got "int", expected "Union[bool, str]")
    def f(x) -> int:
        return 4
