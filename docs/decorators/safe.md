# safe

Safe function cannot raise any exceptions. Alias for [raises](raises) without arguments.

```python
@deal.safe
def divide(a, b):
    return a / b

divide(1, 2)
# 0.5

divide(1, 0)
# ZeroDivisionError: division by zero
# The above exception was the direct cause of the following exception:
# RaisesContractError:
```

## Motivation

Can you be sure that some function never raises exceptions? Make promise about this, and `@deal.safe` will help you to control it.
