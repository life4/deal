# post

[Postcondition](https://en.wikipedia.org/wiki/Postcondition) -- condition that must be true after function executed. Raises `PostContractError` otherwise.

```python
@deal.post(lambda x: x > 0)
def always_positive_sum(*args):
    return sum(args)

always_positive_sum(2, -3, 4)
# 3

always_positive_sum(2, -3, -4)
# PostContractError:
```


## Motivation

Make constraints about function response.

Bad:

```python
def get_usernames(role):
    if role != 'admin':
        return dict(code=403)
    return dict(records=['oleg', 'greg', 'admin'])

def some_other_code(role):
    response = get_usernames(role)
    if 'code' not in response:
        response['code'] = 200
    ...
```

Good:

```python
@deal.post(lambda resp: type(resp) is dict)
@deal.post(lambda resp: 'code' in resp)
@deal.post(lambda resp: 'records' in resp)
def get_usernames(role):
    if role != 'admin':
        return dict(code=403, records=[])
    return dict(code=200, records=['oleg', 'greg', 'admin'])

def some_other_code(role):
    response = get_usernames(role)
    ...
```
