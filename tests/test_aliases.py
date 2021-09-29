from inspect import getdoc
from typing import get_type_hints

import pytest

import deal


def get_func():
    @deal.pre(lambda x: x > 0)
    @deal.post(lambda x: x > 0)
    @deal.ensure(lambda *args, **kwargs: True)
    @deal.raises(ValueError)
    @deal.safe
    @deal.safe()
    @deal.pure
    @deal.chain(deal.safe, deal.pure)
    def func(x: int) -> int:
        """docs were before docker
        """
        return x

    return func


def test_preserve_type_annotations():
    """
    IMPORTANT: this checks preserving type annotations in runtime.
    mypy is a static analyser and can produce a different result.
    """
    func = get_func()
    annotations = get_type_hints(func)
    assert set(annotations) == {'x', 'return'}
    assert annotations['x'] in ('int', int)
    assert annotations['return'] in ('int', int)


def test_preserve_docstring():
    func = get_func()
    docs = getdoc(func)
    assert docs is not None
    assert docs.strip() == 'docs were before docker'


def test_implies():
    @deal.pre(lambda x, y: deal.implies(x, y))
    def f(x, y):
        pass

    f(True, True)
    f(False, True)
    f(False, False)
    with pytest.raises(deal.PreContractError):
        f(True, False)


def test_catch():
    def div(x, y):
        return x / y

    assert deal.catch(div, 1, 2) is None
    assert deal.catch(div, 1, y=2) is None
    assert deal.catch(div, x=1, y=2) is None
    assert deal.catch(div, 1, 0) is ZeroDivisionError
