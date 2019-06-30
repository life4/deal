# offline

Offline function cannot do network requests. This is achieved by patching `socket.socket`. So, don't use it into asynchronous or multi-threaded code.

```python
@deal.offline
def ping(host):
    if host == 'localhost':
        return True
    response = requests.head('http://' + host)
    return response.ok

ping('localhost')
# True

ping('ya.ru')
# OfflineContractError:
```
