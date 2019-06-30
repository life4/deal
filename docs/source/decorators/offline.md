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

## Motivation

Sometimes, your code are doing unexpected network requests. Use `@offline` to catch these cases to do code optimization if possible.

Bad:

```python
def get_genres():
    response = requests.get('http://example.com/genres.txt')
    response.raise_for_status()
    return response.text.splitlines()

def valid_genre(genre):
    ...
    return genre in get_genres()

def validate_genres(genres):
    return all(valid_genre(genre) for genre in genres)
```

Good:

```python
def get_genres():
    response = requests.get('http://example.com/genres.txt')
    response.raise_for_status()
    return response.text.splitlines()

@deal.offline
def valid_genre(genre, genres):
    ...
    return genre in genres

def validate_genres(genres):
    existing_genres = get_genres()
    return all(valid_genre(genre, existing_genres) for genre in genres)
```
