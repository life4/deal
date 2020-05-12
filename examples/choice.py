import random
from typing import List

import pytest
import deal


@deal.pre(lambda items: bool(items))
@deal.ensure(lambda items, result: result in items)
@deal.has()
def choice(items: List[str]) -> str:
    return random.choice(items)


@pytest.mark.parametrize('case', deal.cases(choice))
def test_choice(case):
    case()
