# Exceptions

## deal.raises

`@deal.raises` specifies which exceptions the function can raise.

```python
@deal.raises(ZeroDivisionError)
def divide(*args):
    return sum(args[:-1]) / args[-1]

divide(1, 2, 3, 6)
# 1.0

divide(1, 2, 3, 0)
# ZeroDivisionError: division by zero

divide()
# IndexError: tuple index out of range
# The above exception was the direct cause of the following exception:
# RaisesContractError:
```

`@deal.raises()` without exceptions specified means that function raises no exception.

## deal.reason

Checks condition if exception was raised.

```python run
@deal.reason(ZeroDivisionError, lambda a, b: b == 0)
def divide(a, b):
    return a / b
```

## Motivation

Exceptions are the most implicit part of Python. Any code can raise any exception. None of the tools can say you which exceptions can be raised in some function. However, sometimes you can infer it yourself and say it to other people. And `@deal.raises` will remain you if function has raised something that you forgot to specify.

Also, it's an important decorator for autotesting. Deal won't fail tests for exceptions that were marked as allowed with `@deal.raises`.
