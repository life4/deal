# pure

Pure function cannot do network requests, write anything into stdout or raise any exceptions. It gets some parameters and returns some result. That's all. In runtime, it does the same checks as `chain(safe, silent, offline)`. However, [linter](../commands/lint) checks a bit more, like no `import`, `global`, `nonlocal`, etc.

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
