import deal


def preserve_function_annotation() -> None:
    @deal.inv(lambda obj: obj.likes >= 0)
    class Video:
        likes: int

    v = Video()
    reveal_type(v)  # R: types_inv.Video@6


def infer_validator_type() -> None:
    # E: "Video" has no attribute "hello"
    @deal.inv(lambda obj: obj.hello)
    class Video:
        likes: int
