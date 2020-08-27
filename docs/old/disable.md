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

Also, you can explicitly enable or disable contracts:

```python
# disable contracts without `debug=True`
deal.switch(main=False)

# enable contracts with `debug=True`
deal.switch(debug=True)

# disable contracts with `debug=True`
deal.switch(debug=False)

# disable all contracts
deal.switch(main=False, debug=False)

# return default behavior
# (`main` enabled, `debug` the same as `__debug__`)
deal.reset()
```
