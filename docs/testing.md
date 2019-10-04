# Testing

Deal can automatically test your functions. First of all, your function has to be prepared:

1. All function arguments are type-annotated.
1. All exceptions that function can raise are specified in [@deal.raises](decorators/raises).
1. All pre-conditions are specified with [@deal.pre](decorators/pre).

Then use `deal.cases` to get test cases for the function. Every case is a callable object that gets no arguments. Calling it will call the original function with suppressing allowed exceptions.

## Example

```python
@deal.raises(ZeroDivisionError)
@deal.pre(lambda a, b: a > 0 and b > 0)
def div(a: int, b: int) -> float:
    return a / b


for case in deal.cases(div):
    case()
```

## pytest

A simple snippet to use `deal.cases` with pytest (type annotations are optional):

```python
@pytest.mark.parametrize('case', deal.cases(div))
def test_div(case: deal.TestCase) -> None:
    case()
```

## How it works

1. Deal generates random values for all function arguments with [hypothesis](https://hypothesis.readthedocs.io/en/latest/).
1. For every arguments combination `deal.cases` returns `deal.TestCase` object.
1. `deal.TestCase` on calling is doing the next steps:
    1. Calling the original function with all decorators and contracts.
    1. Suppressing exceptions from `deal.pre` and `deal.raises`. In that case `typing.NoReturn` returned.
    1. Validating type of the function result if it's annotated.
    1. Returning the function result.

All uncatched exceptions are raised: everything you forgot to specify in `@deal.raises`, `deal.PostContractError`, `deal.OfflineContractError` etc.

## Configuring

Specify samples count (50 by default):

```python
deal.cases(div, count=20)
```

Explicitly specify arguments to pass into the function:

```python
deal.cases(div, kwargs=dict(b=3))
```
