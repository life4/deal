# silent

Silent function cannot write anything into stdout. This is achieved by patching `sys.stdout`. So, don't use it into asynchronous or multi-threaded code.

```python
@deal.silent
def has_access(role):
    if role not in ('user', 'admin'):
        print('role not found')
        return False
    return role == 'admin'

has_access('admin')
# True

has_access('superuser')
# SilentContractError:
```

## Motivation

If possible, avoid any output from function. Direct output makes debugging and re-usage much more difficult. Of course, there are some exceptions:

1. Entry-points that communicate with user and never should be used from other code.
1. Logging. Logging also output, but this output makes our life easier. However, be sure, you're not using logging for something important that should be checked from other code or tested.

Bad:

```python
def say_hello(name):
    print('Hello, {name}')

def main():
    say_hello(sys.argv[1])
```

Good:

```python
@deal.silent
def make_hello(name):
    return 'Hello, {name}'

def main(argv=None):
    if argv is None:
        argv = sys.argv[1:]
    print(make_hello(argv[0]))
```
