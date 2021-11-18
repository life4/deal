import ast
from textwrap import dedent

import astroid
import pytest

from deal.linter._contract import Category, Contract
from deal.linter._func import Func


TEXT = """
import deal

@deal.raises(ValueError, UnknownError, idk_what_is_it())
@notadeal.raises(KeyError)
def f(x):
    return x
"""


def test_exceptions():
    funcs1 = Func.from_ast(ast.parse(TEXT))
    assert len(funcs1) == 1
    funcs2 = Func.from_astroid(astroid.parse(TEXT))
    assert len(funcs2) == 1
    for func in (funcs1[0], funcs2[0]):
        assert len(func.contracts) == 1
        contract = func.contracts[0]
        assert contract.exceptions == [ValueError, 'UnknownError']


def test_repr():
    c = Contract(
        category=Category.RAISES,
        args=[],
        func_args=None,  # type: ignore[arg-type]
    )
    assert repr(c) == 'Contract(raises)'


def test_run():
    text = """
    import deal

    @deal.post(lambda x: x > 0)
    def f(x):
        return x
    """
    text = dedent(text).strip()
    funcs1 = Func.from_ast(ast.parse(text))
    assert len(funcs1) == 1
    funcs2 = Func.from_astroid(astroid.parse(text))
    assert len(funcs2) == 1
    for func in (funcs1[0], funcs2[0]):
        assert len(func.contracts) == 1
        c = func.contracts[0]
        assert c.run(1) is True
        assert c.run(-1) is False


def test_resolve_func():
    text = """
    import deal

    def contract(x):
        return x > 0

    @deal.post(contract)
    def f(x):
        ...
    """
    text = dedent(text).strip()
    funcs = Func.from_astroid(astroid.parse(text))
    assert len(funcs) == 2
    func = funcs[-1]
    assert len(func.contracts) == 1
    c = func.contracts[0]
    assert c.run(1) is True
    assert c.run(-1) is False


def test_resolve_lambda():
    text = """
    import deal

    contract = lambda x: x > 0

    @deal.post(contract)
    def f(x):
        ...
    """
    text = dedent(text).strip()
    funcs = Func.from_astroid(astroid.parse(text))
    assert len(funcs) == 1
    func = funcs[0]
    assert len(func.contracts) == 1
    c = func.contracts[0]
    assert c.run(1) is True
    assert c.run(-1) is False


def test_return_message():
    text = """
    import deal

    @deal.post(lambda x: x > 0 or 'oh no!')
    def f(x):
        return x
    """
    text = dedent(text).strip()
    funcs1 = Func.from_ast(ast.parse(text))
    assert len(funcs1) == 1
    funcs2 = Func.from_astroid(astroid.parse(text))
    assert len(funcs2) == 1
    for func in (funcs1[0], funcs2[0]):
        assert len(func.contracts) == 1
        c = func.contracts[0]
        assert c.run(1) is True
        assert c.run(-1) == 'oh no!'


def test_simplified_signature():
    text = """
    import deal

    @deal.post(lambda _: _.a > _.b)
    def f(a, b):
        return a + b
    """
    text = dedent(text).strip()
    funcs1 = Func.from_ast(ast.parse(text))
    assert len(funcs1) == 1
    funcs2 = Func.from_astroid(astroid.parse(text))
    assert len(funcs2) == 1
    for func in (funcs1[0], funcs2[0]):
        assert len(func.contracts) == 1
        c = func.contracts[0]
        assert c.run(3, 2) is True
        assert c.run(2, 3) is False


@pytest.mark.parametrize('source, deps', [
    ('lambda: ...', set()),
    ('lambda a, b: ...', {'a', 'b'}),
    ('lambda *args, **kwargs: ...', {'args', 'kwargs'}),
    ('lambda a, *, b: ...', {'a', 'b'}),
])
def test_arguments(source: str, deps: set):
    text = """
    import deal

    @deal.post({source})
    def f():
        return 2
    """
    text = text.format(source=source)
    text = dedent(text).strip()

    tree = ast.parse(text)
    print(ast.dump(tree))
    funcs1 = Func.from_ast(tree)

    tree = astroid.parse(text)
    print(tree.repr_tree())
    funcs2 = Func.from_astroid(tree)

    for funcs in (funcs1, funcs2):
        assert len(funcs) == 1
        func = funcs[0]
        assert len(func.contracts) == 1
        c = func.contracts[0]
        assert c.arguments == deps


@pytest.mark.parametrize('source, deps', [
    ('lambda a, b: cd', {'cd'}),
    ('lambda a, b: a+b', set()),
    ('lambda a, b: (a+b)/c', {'c'}),

    ('lambda: re.compile()', {'re'}),
    ('lambda a, b: ab.cd()', {'ab'}),
])
def test_dependencies(source: str, deps: set):
    text = """
    import deal

    @deal.post({source})
    def f(a, b):
        return a + b
    """
    text = text.format(source=source)
    text = dedent(text).strip()
    funcs1 = Func.from_ast(ast.parse(text))

    tree = astroid.parse(text)
    print(tree.repr_tree())
    funcs2 = Func.from_astroid(tree)

    for funcs in (funcs1, funcs2):
        assert len(funcs) == 1
        func = funcs[0]
        assert len(func.contracts) == 1
        c = func.contracts[0]
        assert c.dependencies == deps


def test_resolve_and_run_dependencies_func_astroid():
    text = """
    import deal
    CONST = 34

    def contract(a):
        return a == CONST

    @deal.post(contract)
    def f(a):
        return a * 2
    """
    text = dedent(text).strip()
    tree = astroid.parse(text)
    print(tree.repr_tree())
    funcs = Func.from_astroid(tree)
    assert len(funcs) == 2
    func = funcs[-1]
    assert len(func.contracts) == 1
    c = func.contracts[0]

    assert c.run(12) is False
    assert c.run(34) is True


def test_resolve_and_run_dependencies_lambda():
    text = """
    import deal

    CONST = 34

    @deal.post(lambda a: a == CONST)
    def f(a):
        return a * 2
    """
    text = dedent(text).strip()
    funcs1 = Func.from_ast(ast.parse(text))

    tree = astroid.parse(text)
    print(tree.repr_tree())
    funcs2 = Func.from_astroid(tree)

    for funcs in (funcs1, funcs2):
        assert len(funcs) == 1
        func = funcs[0]
        assert len(func.contracts) == 1
        c = func.contracts[0]

        assert c.run(12) is False
        assert c.run(34) is True


def test_lazy_import_stdlib():
    text = """
    import deal

    @deal.post(lambda a: re.compile('^abc$').match(a))
    def f(a):
        return a * 2
    """
    text = dedent(text).strip()
    funcs = Func.from_ast(ast.parse(text))
    assert len(funcs) == 1
    func = funcs[0]
    assert len(func.contracts) == 1
    c = func.contracts[0]

    assert c.run('bcd') is False
    assert c.run('abc') is True


def test_unresolvable():
    text = """
    import deal

    @deal.post(lambda a: re.compile(unknown))
    def f(a):
        return a * 2
    """
    text = dedent(text).strip()
    funcs = Func.from_ast(ast.parse(text))
    assert len(funcs) == 1
    func = funcs[0]
    assert len(func.contracts) == 1
    c = func.contracts[0]

    with pytest.raises(NameError):
        c.run('bcd')
