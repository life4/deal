# Side-effects

## deal.has

`@deal.has` is a way to specify markers for a function. Markers are tags about kinds of side-effects which the function has. For example:

```python
@deal.has('stdout', 'database')
def say_hello(id: int) -> None:
    user = get_user(id=id)
    print(f'Hello, {user.name}')
```

You can use any markers you want, and Deal will check that if you call a function with some markers, they are specified for the calling function as well. In the example above, `print` function has marker `stdout`, so it must be specified in markers of `say_hello` as well.

## Motivation

Every application has side-effects. It needs to store data, to communicate with users. However, every side-effect makes testing and debugging much harder: it should be mocked, intercepted, cleaned after every test. The best solution is to have [functional core and imperative shell](https://www.destroyallsoftware.com/screencasts/catalog/functional-core-imperative-shell). So, the function above can be refactored to be pure:

```python
# now this is pure
@deal.has()
def make_hello(user) -> str:
    return f'Hello, {user.name}'

# and the main function takes care of all impure things
@deal.has('stdout', 'database')
def main(stream=sys.stdout):
    ...
    user = get_user(id=id)
    hello = make_hello(user=user)
    print(make_hello, file=stream)
```

## Built-in markers

Deal already know about some markers and will report if they are violated:

```eval_rst
+---------+--------------+----------------------------------+
| code    | marker       | allows                           |
+=========+==============+==================================+
| DEAL042 | `io`         | everything below                 |
+---------+--------------+----------------------------------+
| DEAL043 | -- `read`    | read a file                      |
+---------+--------------+----------------------------------+
| DEAL044 | -- `write`   | write into a file                |
+---------+--------------+----------------------------------+
| DEAL045 | -- `stdout`  | `sys.stdout` and `print`         |
+---------+--------------+----------------------------------+
| DEAL046 | -- `stderr`  | `sys.stderr`                     |
+---------+--------------+----------------------------------+
| DEAL047 | -- `network` | network communications, `socket` |
+---------+--------------+----------------------------------+
| DEAL051 | `global`     | `global` and `nonlocal`          |
+---------+--------------+----------------------------------+
| DEAL052 | `import`     | `import`                         |
+---------+--------------+----------------------------------+
```

## Exceptions

What you should know:

+ For every marker deal raises its own exception.
+ Every such exception is inherited from `MarkerError`.
+ `MarkerError` inherited from `ContractError`.
+ `ContractError` inherited from built-in `AssertionError`.

```eval_rst
+----------+----------------------+
| marker   | exception            |
+==========+======================+
| network  | OfflineContractError |
+----------+----------------------+
| stdout   | SilentContractError  |
+----------+----------------------+
| stderr   | SilentContractError  |
+----------+----------------------+
```

Quick Q&A session:

+ **Question:** When should I worry about exception type raised by a contract?
  + **Answer:** Never.
+ **Question:** Where are other markers? What are their exceptions?
  + **Answer:** Other markers aren't checked in runtime yet. Don't worry, you still have [linter](./linter.md).

## Markers are properties

Markers and exceptions are properties of a function and don't depend on conditions. That means, if a function only sometimes in some conditions does io operation, the function has `io` marker regardless of possibility of hitting this condition branch. For example:

```python
import deal

def run_job(job_name: str, silent: bool):
    if not silent:
        print('job started')
    ...

@deal.has()  # must have 'stdout' here.
def main():
    job_name = 'hello'
    run_job(job_name, silent=True)
    return 0
```

If we run [linter](./linter.md) on the code above, it will fail with "DEAL046 missed marker (stdout)" message. `main` function calls `run_job` with `silent=True` so `print` will not be called when calling `main`. However, `run_job` function has an implicit `stdout` marker, and `main` calls this function so it must have this marker as well.
