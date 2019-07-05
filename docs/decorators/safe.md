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
