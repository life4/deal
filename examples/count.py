from typing import List

import deal
import pytest


@deal.post(lambda result: result >= 0)
@deal.has()
def count(items: List[str], item: str) -> int:
    return items.count(item)


@pytest.mark.parametrize('case', deal.cases(count))
def test_count(case: deal.TestCase):
    case()
