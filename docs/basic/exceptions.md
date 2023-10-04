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

## deal.safe

`@deal.safe` is an alias for `@deal.raises()`. Wraps a function that never raises an exception.

## deal.reason

Checks condition if exception was raised.

```python run
@deal.reason(ZeroDivisionError, lambda a, b: b == 0)
def divide(a, b):
    return a / b
```

## Motivation

Exceptions in Python are often implicit. Any part of the code has the potential to raise any exception, and none of the available tools can definitively identify which exceptions might be raised by a particular function. Nevertheless, sometimes you might be able to determine this yourself, and use the `@deal.raises` decorator to communicate it. The decorator also serves as a reminder if a function raises an exception that hasn't been explicitly specified. Furthermore, this decorator is valuable for auto-testing: `deal` won't flag tests as failures if exceptions are raised that have been permitted using `@deal.raises`.
