# Runtime

...

## Contracts on production

If you run Python with `-O` option, all contracts will be disabled. This is uses Python's `__debug__` option:

> The built-in variable `__debug__` is True under normal circumstances, False when optimization is requested (command line option -O).
> Source: [Python documentation](https://docs.python.org/3/reference/simple_stmts.html#assert)

Also, you can explicitly enable or disable contracts:

```python
# disable all contracts
deal.disable()

# enable all contracts
deal.enable()

# restore the default behavior
# (enabled if `__debug__` is True, disabled otherwise)
deal.reset()
```
