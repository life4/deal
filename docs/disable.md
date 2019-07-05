# Disable contracts on production

If you want disable contracts on production, pass `debug=True` to decorator:

```python
@deal.post(lambda x: x > 0, debug=True)
def my_sum(*args):
    return sum(args)
```

If you run Python with `-O` option, contracts will be disabled. This is uses Python's `__debug__` option:

> The built-in variable `__debug__` is True under normal circumstances, False when optimization is requested (command line option -O).
> - [Official documentation](https://docs.python.org/3/reference/simple_stmts.html#assert)
