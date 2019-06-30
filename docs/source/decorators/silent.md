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
