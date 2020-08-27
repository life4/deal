# chain

Beautiful way to apply a few short decorators to a function.

```python
@deal.chain(deal.safe, deal.silent)
def show_division(a, b):
    print(a / b)

show_division(1, 2)
# SilentContractError:

show_division(1, 0)
# RaisesContractError:
```

## Motivation

Get rid of long chains of decorators because it looks like centipede. Use `@chain` to place short decorators horizontally.
