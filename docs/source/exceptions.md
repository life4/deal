## Exceptions

Every contract type has it's own exception type. Every exception inherited from `ContractError`. `ContractError` inherited from built-in `AssertionError`.

Custom error message for any contract can be specified by `message` argument:

```python
@deal.pre(lambda name: name.lower() != 'oleg', message='user name cannot be Oleg')
def hello(name):
    print(f'hello, {name}')

hello('Oleg')
# PreContractError: user name cannot be Oleg
```

Custom exception for any contract can be specified by `exception` argument:

```python
@deal.pre(lambda role: role in ('user', 'admin'), exception=LookupError)
def change_role(role):
    print(f'now you are {role}!')

change_role('superuser')
# LookupError:
```

Also, contract can return string, and this string will be used as error message:

```python
def contract(name):
    if name.lower() == 'oleg':
        return 'not today, Oleg'
    if name in ('admin', 'moderator'):
        return 'this name is reservered'
    return True

@deal.pre(contract)
def register(name):
    print(f'welcome on board, {name}!')

register('Greg')
# welcome on board, Greg!

register('Oleg')
# PreContractError: not today, Oleg
```
