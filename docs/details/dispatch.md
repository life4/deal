# Dispatch

```{warning}
This feature is **experimental**. It works and the API is stable but the behavior in some corner cases may change in the future.
```

The decorator `deal.dispatch` allows combining multiple implementations of a function into one. When the combined function is called, deal will try to execute every implementation and return the result of the first one that hasn't raised `PreContractError`.

```python run
@deal.dispatch
def age2stage(age: int) -> str:
    raise NotImplementedError

@age2stage.register
@deal.pre(lambda age: age < 12)
def _(age: int) -> int:
    return 'kid'

@age2stage.register
@deal.pre(lambda age: age < 18)
def _(age: int) -> int:
    return 'teen'

age2stage(10)  # 'kid'
age2stage(14)  # 'teen'
```

If the given arguments passed preconditions for none of the implementations, `NoMatchError` is raised:

```python
age2stage(20)
# NoMatchError: expected age < 12 (where age=20); expected age < 18 (where age=20)
```

To avoid it, just add a default implementation:

```python
@age2stage.register
def _(age: int) -> int:
    return 'adult'

age2stage(20)  # 'adult'
```

The initially decorated function (which you directly pass into `@deal.dispatch`) is never executed. It is used only to provide the name, docstring, and type annotations for the combined function. However, we specify `raise NotImplementedError` instead of just `pass` as the function body, so type checkers won't complain about invalid return type.

Since dispatch requires contracts to be enabled, when you call a dispatched function, contracts get forcefully enabled for the function duration. It may be changed in the future to enable only needed {py:func}`deal.pre` contracts. So, keep it in mind: if you want to disable all contracts on the production all together, `deal.dispatch` could be a bad fit for your application.

## Motivation

The decorator was introduced as a way to do the same as [functools.singledispatch] but using preconditions instead of types. It gives you much more flexibility, allowing you to implement anything you could do in some other languages with the combination of [pattern matching], [guards], and [function overloading]. A classic example is recursively calculating factorial.

In Elixir:

```elixir
defmodule Math do
    @spec fac(integer) :: integer
    @doc """
    Calculate factorial of the given number.
    """
    def fac(0), do: 1
    def fac(n) when n > 0, do: n * fac(n - 1)
end

Math.fac(5)   # 120
Math.fac(-1)  # FunctionClauseError
```

And the same in Python using `deal.dispatch`:

```python
@deal.dispatch
def fac(n: int) -> int:
    """Calculate factorial of the given number.
    """
    raise NotImplementedError

@fac.register
@deal.pre(lambda n: n == 0)
def _(n):
    return 1

@fac.register
@deal.pre(lambda n: n > 0)
def _(n):
    return n * fac(n - 1)

fac(5)   # 120
fac(-1)  # NoMatchError
```

The implementation based on `deal.dispatch` is more verbose. However, it pays back when each implementation is complex. For example, reading a config in different formats.

Simple solution:

```python
from pathlib import Path

def read_config(path: Path) -> Config:
    if path.suffix == '.json':
        ...
    if path.suffix in {'.yml', '.yaml'}:
        ...
    raise ValueError
```

And solution with dispatch:

```python
@deal.dispatch
def read_config(path: Path) -> Config:
    raise NotImplementedError

@read_config.register
@deal.pre(lambda path: path.suffix == '.json')
def read_json(path):
    ...

@read_config.register
@deal.pre(lambda path: path.suffix in {'.yml', '.yaml'})
def read_yaml(path):
    ...
```

The latter gives multiple benefits:

1. Each implementation is isolated from others, and so it is easier to read and maintain.
1. Each implementation can be called directly, by users of from tests.
1. Pre-conditions are attached to implementations rather than the `read_config` function, so even if an implementation is called directly, we still can be sure that it is used correctly.
1. Users can register new implementations. So, you have a plugins system out of the box.

[functools.singledispatch]: https://docs.python.org/3/library/functools.html#functools.singledispatch
[pattern matching]: https://en.wikipedia.org/wiki/Pattern_matching
[guards]: https://en.wikipedia.org/wiki/Guard_(computer_science)
[function overloading]: https://en.wikipedia.org/wiki/Function_overloading
