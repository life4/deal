# @inv

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
