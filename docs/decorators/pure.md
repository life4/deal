# pure

Pure function cannot do network requests, write anything into stdout or raise any exceptions. It gets some parameters and returns some result. That's all. This is alias for `chain(safe, silent, offline)`.

```python
@deal.pure
def show_division(a, b):
    print(a / b)

show_division(1, 2)
# SilentContractError:

show_division(1, 0)
# RaisesContractError:
```

## Motivation

Explicitly mark pure functions in your code. Pure functions easier to test and safer to use.
