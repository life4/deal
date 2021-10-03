# Contract-Driven Development

Let's take for example an incredibly simple code and imagine that it's incredibly complicated logic.

```python run
def cat(left, right):
    """Concatenate two given strings.
    """
    return left + right
```

## Tests

How can we be sure this code works? No, it's not obvious. Remember the rules of the game, we have an incredibly complicated realization. So, we can't say it works or not while we haven't tested it.

```python run
def test_cat():
    result = cat(left='abc', right='def')
    assert result == 'abcdef'
```

Now, run [pytest](https://docs.pytest.org/en/latest/):

```bash
pytest cat.py
```

It passes. So, our code works. Right?

## Table tests

Wait, but what about corner cases? What if one string is empty? What if both strings are empty? What if we have only one character in both strings? We need check more values and this is where [table driven tests](https://dave.cheney.net/2019/05/07/prefer-table-driven-tests) will save our time. In pytest, we can use [@pytest.mark.parametrize](https://docs.pytest.org/en/latest/parametrize.html#pytest-mark-parametrize) to make such tables.

```python run
import pytest

@pytest.mark.parametrize('left, right, expected', [
    ('a', 'b', 'ab'),
    ('', '', ''),
    ('', 'b', 'b'),
    ('a', '', 'a'),
    ('text', 'check', 'textcheck'),
])
def test_cat(left, right, expected):
    result = cat(left=left, right=right)
    assert result == expected
```

## Properties

Table tests can be enormously long, and for every test case, we have to manually calculate the expected result. For complicated code, it's a lot of work. Can we do it better and think and write less? Yes, we can instead of _expected result_ talk about _expected properties of the result_. The big difference is the result is different for different input values, but properties always the same. The coolest thing is in most cases you already know result properties, it is the business requirements, and your code is no more than the implementation of these requirements.

So, what are the properties of our function?

1. The result string starts with the first given string.
1. The result string ends with the second given string.
1. Result string has the length equal to the sum of lengths of given strings.

Now, we can check these properties for the result instead of checking particular values.

```python run
@pytest.mark.parametrize('left, right', [
    ('a', 'b'),
    ('', ''),
    ('', 'b'),
    ('a', ''),
    ('text', 'check'),
])
def test_cat(left, right):
    result = cat(left=left, right=right)
    assert result.startswith(left)
    assert result.endswith(right)
    assert len(result) == len(left) + len(right)
```

## Hypothesis

We've tested a few corner cases but not all of them. What about Unicode strings? What if one string is Unicode, but another one isn't? What about spaces? What if we have a string termination symbol somewhere? What if both strings contain only digits (the place where JS always surprises)? It's so hard to find examples for all possible cases where something can go wrong. In theory, you even can't say that it works while you haven't checked **all** possible values (that impossible even for our simple function). So, instead of trying to figure out all possible nightly values we can ask the machine to do so. This is where the [property-based testing](https://dev.to/jdsteinhauser/intro-to-property-based-testing-2cj8) comes in. In Python, we have a great tool [hypothesis](https://hypothesis.readthedocs.io/en/latest/) that can generate test examples for us:

```python
import hypothesis
from hypothesis import strategies

@hypothesis.given(left=strategies.text(), right=strategies.text())
def test_cat(left, right):
    result = cat(left=left, right=right)
    assert result.startswith(left)
    assert result.endswith(right)
    assert len(result) == len(left) + len(right)
```

## Type annotations

Another one cool thing in Python we have to talk about before moving further is [type annotations](https://dev.to/dstarner/using-pythons-type-annotations-4cfe):

```python run
def cat(left: str, right: str) -> str:
    return left + right
```

Type annotations aren't perfect and can be too complicated. However, what is most important is now humans and machines know much more about your code. You can run [mypy](https://github.com/python/mypy) and check that you haven't made type errors. And the thing is it's not only about catching type errors. Now we can use [hypothesis-auto](https://timothycrosley.github.io/hypothesis-auto/) wrapper around hypothesis. It will infer parameters types and explain names and types of parameters to Hypothesis. So, instead of writing `hypothesis.given(left=strategies.text(), right=strategies.text())` we can just say `hypothesis_auto.auto_pytest(cat)`.

```python
import hypothesis_auto

@hypothesis_auto.auto_pytest(cat)
def test_cat(test_case):
    result = test_case()
    left = test_case.parameters.kwargs['left']
    right = test_case.parameters.kwargs['right']
    assert result.startswith(left)
    assert result.endswith(right)
    assert len(result) == len(left) + len(right)
```

It looks longer because now parameters are placed inside the long name `test_case.parameters.kwargs` but the most important thing here is we don't talk about function inputs at all, the machine does everything. The test isn't about any values of the function anymore but only about the function properties.

## Contracts

Can we make it even simpler? Not really. The implementation can produce some values, and the machine can infer some properties of the result. However, someone else must say which properties are good and expected, and which are not. However, there is something else about our properties that we can do better. At this stage we have type annotations and, to be honest, they are just kind of properties. Annotations say "the result is a text", and our test properties clarify the length of the result, it's prefix and suffix. However, the difference is type annotations are the part of the function itself. It gives some benefits:

1. The machine can check statically, without the actual running of the code.
1. The human can see types (think "possible values set") for arguments and the result.

And Deal can make the same for function properties:

```python run
import deal

@deal.ensure(lambda left, right, result: result.startswith(left))
@deal.ensure(lambda left, right, result: result.endswith(right))
@deal.ensure(lambda left, right, result: len(result) == len(left) + len(right))
def cat(left: str, right: str) -> str:
    return left + right
```

Or using short signatures:

```python run
import deal

@deal.ensure(lambda _: _.result.startswith(_.left))
@deal.ensure(lambda _: _.result.endswith(_.right))
@deal.ensure(lambda _: len(_.result) == len(_.left) + len(_.right))
def cat(left: str, right: str) -> str:
    return left + right
```

Now, it's not just properties, but [contracts](https://en.wikipedia.org/wiki/Design_by_contract). They can be checked in the runtime, simplify tests, tell humans about the function behavior. And tests for this implementation are trivial:

```python
test_cat = deal.cases(cat)
```

## Contracts for machines

The most exciting thing is deal can check contracts statically, like mypy checks annotations. However, contracts can be any code while types are [standardized and limited](https://docs.python.org/3/library/typing.html). Although the machine can't check everything (yet), it can catch some trivial cases. For example:

```python run
@deal.post(lambda result: 0 <= result <= 1)
def sin(x):
    return 2
```

And when we run [deal linter](linter) on this code, we see contract violation error:

```bash
❯ flake8 --show-source sin.py
sin.py:6:5: DEAL011: post contract error
    return 2
    ^
```
