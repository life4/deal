# Values

## deal.pre

[Precondition](https://en.wikipedia.org/wiki/Precondition) -- condition that must be true before the function is executed.

```python
@deal.pre(lambda *args: all(arg > 0 for arg in args))
def sum_positive(*args):
    return sum(args)

sum_positive(1, 2, 3, 4)
# 10

sum_positive(1, 2, -3, 4)
# PreContractError: expected all(arg > 0 for arg in args) (where args=(1, 2, -3, 4))
```

## deal.post

[Postcondition](https://en.wikipedia.org/wiki/Postcondition) -- condition that must be true after the function was executed. Raises `PostContractError` otherwise.

```python
@deal.post(lambda x: x > 0)
def always_positive_sum(*args):
    return sum(args)

always_positive_sum(2, -3, 4)
# 3

always_positive_sum(2, -3, -4)
# PostContractError:
```

Post-condition allows you to make additional constraints about a function result. Use type annotations to limit types of results and post-conditions to limit possible values inside given types.

## deal.ensure

Ensure is a postcondition that accepts not only result, but also function arguments. Must be true after function executed.

```python
@deal.ensure(lambda x, result: x != result)
def double(x):
    return x * 2

double(2)
# 4

double(0)
# PostContractError: expected x != result (where result=0, x=0)
```

Ensure is the shining star of property-based testing. It works perfect for [P vs NP](https://en.wikipedia.org/wiki/P_versus_NP_problem) like problems. In other words, for complex task when checking result correctness (even partial checking only for some cases) is much easier then the calculation itself.

## deal.inv

[Invariant](https://en.wikipedia.org/wiki/Invariant) -- condition that can be relied upon to be true during execution of a program.

Invariant check condition in the next cases:

1. Before class method execution.
1. After class method execution.
1. After some class attribute setting.

```python
@deal.inv(lambda post: post.likes >= 0)
class Post:
    likes = 0

post = Post()

post.likes = 10

post.likes = -10
# InvContractError: expected post.likes >= 0

type(post)
# deal.core.PostInvarianted
```

## assert

Good old [assert statement](https://docs.python.org/3/reference/simple_stmts.html#the-assert-statement) is also kind of a contract. It is good for checking intermediate state inside a function. Also, it is similar to other contracts since deal mimics `assert` behavior: all contracts are [disabled on production](./runtime.md) and raise [AssertionError](https://docs.python.org/3/library/exceptions.html#AssertionError) in case of the contract violation. Also, [deal linter](linter.md) checks `assert` statements to be True.

```python run
def do_something(a):
    result = something_else(a)
    assert result > 0
    return another_thing(result)
```

## Exceptions

Every contract type raises it's own exception type, inherited from `ContractError` (which is inherited from built-in `AssertionError`):

| contract | exception         |
| -------- | ----------------- |
| pre      | PreContractError  |
| post     | PostContractError |
| ensure   | PostContractError |
| inv      | InvContractError  |

Custom exception for any contract can be specified by `exception` argument:

```python
@deal.pre(lambda role: role in ('user', 'admin'), exception=LookupError)
def change_role(role):
    print(f'now you are {role}!')

change_role('superuser')
# LookupError:
```

However, thumb-up rule is to avoid catching exceptions from contracts. Contracts aren't part of business logic, but are validation. Hence, a contract error means a business logic violation has occurred and execution should be stopped to avoid doing something not predicted and even dangerous.

## Chaining contracts

You can chain any contracts:

```python
@deal.pre(lambda x: x > 0)
@deal.pre(lambda x: x < 10)
def f(x):
    return x * 2

f(5)
# 10

f(-1)
# PreContractError: expected x > 0 (where x=-1)

f(12)
# PreContractError: expected x < 10 (where x=12)
```

`@deal.post` and `@deal.ensure` contracts are resolved from bottom to top. All other contracts are resolved from top to bottom. This is because of how wrapping works: before calling function we go down the contracts list, and after calling the function we go back up the call stack.

## Generators and async functions

Contracts mostly support generators (`yield`) and async functions:

```{eval-rst}
+----------+----------------------------------+------------------------------+
| contract | yield                            | async                        |
+==========+==================================+==============================+
| pre      | yes                              | yes                          |
+----------+----------------------------------+------------------------------+
| post     | yes (checks every yielded value) | yes                          |
+----------+----------------------------------+------------------------------+
| ensure   | yes (checks every yielded value) | yes                          |
+----------+----------------------------------+------------------------------+
| inv      | partially (before execution)     | partially (before execution) |
+----------+----------------------------------+------------------------------+
```
