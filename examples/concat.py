import deal
import pytest


@deal.ensure(lambda _: _.result.startswith(_.left))
@deal.ensure(lambda _: _.result.endswith(_.right))
@deal.has()
def concat(left: str, right: str) -> str:
    return left + right


# TESTS


@pytest.mark.parametrize('case', deal.cases(concat))
def test_concat(case):
    case()
