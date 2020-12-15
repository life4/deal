from typing import List

import hypothesis

import deal


@deal.pre(lambda items: len(items) > 0)
@deal.has()
def my_min(items: List[int]) -> int:
    return min(items)


@hypothesis.example([1, 2, 3])
@deal.cases(
    func=my_min,
    settings=hypothesis.settings(
        verbosity=hypothesis.Verbosity.normal,
    ),
)
def test_min(case):
    case()


if __name__ == '__main__':
    test_min()
