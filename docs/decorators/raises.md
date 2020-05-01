# raises

Specifies which exceptions function can raise.


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

It works the same for generators and async functions.

## Motivation

Exceptions are the most explicit part of Python. Any code can raise any exception. None of the tools can say you which exceptions can be raised in some function. However, sometimes you can infer it yourself and say it to other people. And `@deal.raises` will remain you if function has raised something that you forgot to specify.

Also, it's the most important decorator for [autotesting](../testing). Deal won't fail tests for exceptions that was marked as allowed with `@deal.raises`.

Bad:

```python
ROLES = {
    'admin': 'admin',
    'oleg': 'user',
    'greg': 'user',
}

def get_role(username):
    return ROLES[username]
```

Good:

```python
ROLES = {
    'admin': 'admin',
    'oleg': 'user',
    'greg': 'user',
}

@deal.raises(KeyError)
def get_role(username):
    return ROLES[username]
```
