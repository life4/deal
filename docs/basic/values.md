# Values

## deal.pre

[Precondition](https://en.wikipedia.org/wiki/Precondition) -- condition that must be true before function is executed.

```python
@deal.pre(lambda *args: all(arg > 0 for arg in args))
def sum_positive(*args):
    return sum(args)

sum_positive(1, 2, 3, 4)
# 10

sum_positive(1, 2, -3, 4)
# PreContractError:
```

## deal.post

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

Post-condition allows to make additional constraints about function result. Use type annotations to limit types of result and post-conditions to limit possible values inside given types.

## deal.ensure

Ensure is a postcondition that accepts not only result, but also function arguments. Must be true after function executed.

```python
@deal.ensure(lambda x, result: x != result)
def double(x):
    return x * 2

double(2)
# 4

double(0)
# PostContractError:
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
# InvContractError:

type(post)
# deal.core.PostInvarianted
```

## Simplified signature

The main problem with contracts is that they have to duplicate the original function's signature, including default arguments. While it's not a problem for small examples, things become more complicated when the signature grows. In this case, you can specify a function that accepts only one `_` argument, and deal will pass there a container with arguments of the function call, including default ones:

```python
@deal.pre(lambda _: _.a + _.b > 0)
def f(a, b=1):
    return a + b

f(1)
# 2

f(-2)
# PreContractError:
```

## Exceptions

Every contract type raises it's own exception type, inherited from `ContractError` (which is inherited from built-in `AssertionError`):

```eval_rst
+----------+-------------------+
| contract | exception         |
+==========+===================+
| pre      | PreContractError  |
+----------+-------------------+
| post     | PostContractError |
+----------+-------------------+
| ensure   | PostContractError |
+----------+-------------------+
| inv      | InvContractError  |
+----------+-------------------+
```

Custom exception for any contract can be specified by `exception` argument:

```python
@deal.pre(lambda role: role in ('user', 'admin'), exception=LookupError)
def change_role(role):
    print(f'now you are {role}!')

change_role('superuser')
# LookupError:
```

However, thumb-up rule is to avoid catching exceptions from contracts. Contracts aren't part of business logic but it's validation. Hence contract error means business logic violation and execution should be stopped to avoid doing something not predicted and even dangerous.

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
# PreContractError:

f(12)
# PreContractError:
```

`@deal.post` and `@deal.ensure` contracts are resolved from bottom to top. All other contracts are resolved from top to bottom. This is because of how wrapping works: before calling function we go down by contracts list, after calling the function we go back, up by call stack.

Also, there is `deal.chain` function to chain a few contracts together. It can be helpful to store contracts separately from the function:

```python
contract_for_min = deal.chain(
    deal.pre(lambda items: len(items) > 0),
    deal.ensure(lambda items, result: result in items),
)

@contract_for_min
def min(items):
    ...
```

It can be helpful if a function has too many contracts.

## Generators and async functions

Contracts mostly support generators (`yield`) ans async functions:

```eval_rst
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
