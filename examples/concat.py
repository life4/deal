import deal


@deal.ensure(lambda _: _.result.startswith(_.left))
@deal.ensure(lambda _: _.result.endswith(_.right))
@deal.ensure(lambda _: len(_.result) == len(_.left) + len(_.right))
@deal.has()
def concat(left: str, right: str) -> str:
    """Concatenate 2 given strings.

    https://deal.readthedocs.io/basic/motivation.html
    """
    return left + right


test_concat = deal.cases(concat)
