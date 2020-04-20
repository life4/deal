# ![Deal](https://raw.githubusercontent.com/life4/deal/master/logo.png)

[![Build Status](https://travis-ci.org/life4/deal.svg?branch=master)](https://travis-ci.org/life4/deal) [![Coverage Status](https://coveralls.io/repos/github/life4/deal/badge.svg)](https://coveralls.io/github/life4/deal) [![PyPI version](https://img.shields.io/pypi/v/deal.svg)](https://pypi.python.org/pypi/deal) [![Development Status](https://img.shields.io/pypi/status/deal.svg)](https://pypi.python.org/pypi/deal) [![Code size](https://img.shields.io/github/languages/code-size/life4/deal.svg)](https://github.com/life4/deal)

**Deal** -- python library for [design by contract](https://en.wikipedia.org/wiki/Design_by_contract) (DbC) programming.

That's nice `assert` statements in decorators style to validate function input, output, available operations and object state. Goal is make testing much easier and detect errors in your code that occasionally was missed in tests.

## Features

* [Automatic property-based tests](https://deal.readthedocs.io/testing.html).
* [Static analysis](https://deal.readthedocs.io/linter.html).
* Generators and async coroutines support.
* [External validators support](https://deal.readthedocs.io/validators.html#external-validators).
* [Specify allowed exceptions](https://deal.readthedocs.io/decorators/raises.html) for function
* [Invariant](https://deal.readthedocs.io/decorators/inv.html) for all actions with class instances.
* Decorators to control available resources: forbid [output](https://deal.readthedocs.io/decorators/silent.html), [network operations](https://deal.readthedocs.io/decorators/offline.html), [raising exceptions](https://deal.readthedocs.io/decorators/safe.html).
* You can [disable contracts](https://deal.readthedocs.io/disable.html) on production.

## Available decorators

CLassic DbC:

* [deal.pre](https://deal.readthedocs.io/decorators/pre.html) -- validate function arguments (pre-condition)
* [deal.post](https://deal.readthedocs.io/decorators/post.html) -- validate function return value (post-condition)
* [deal.ensure](https://deal.readthedocs.io/decorators/ensure.html) -- post-condition that accepts not only result, but also function arguments.
* [deal.inv](https://deal.readthedocs.io/decorators/inv.html) -- validate object internal state (invariant).

Take more control:

* [deal.module_load](https://deal.readthedocs.io/decorators/module_load.html) -- check contracts at module initialization.
* [deal.offline](https://deal.readthedocs.io/decorators/offline.html) -- forbid network requests
* [deal.raises](https://deal.readthedocs.io/decorators/raises.html) -- allow only list of exceptions
* [deal.reason](https://deal.readthedocs.io/decorators/reason.html) -- check function arguments that caused a given exception.
* [deal.silent](https://deal.readthedocs.io/decorators/silent.html) -- forbid output into stderr/stdout.

Helpers:

* [`@deal.chain`](https://deal.readthedocs.io/decorators/chain.html) -- chain a few contracts in one.
* [`@deal.pure`](https://deal.readthedocs.io/decorators/pure.html) -- alias for `safe`, `silent`, and `offline`.
* [`@deal.safe`](https://deal.readthedocs.io/decorators/safe.html) -- forbid exceptions.

## Installation

```bash
python3 -m pip install --user deal
```

## Quick Start

```python
import re

import attr
import deal

REX_LOGIN = re.compile(r'^[a-zA-Z][a-zA-Z0-9]+$')

class PostAlreadyLiked(Exception):
    pass

@deal.inv(lambda post: post.visits >= 0)
class Post:
    visits: int = attr.ib(default=0)
    likes: set = attr.ib(factory=set)

    @deal.pre(lambda user: REX_LOGIN.match(user), message='invalid username format')
    @deal.raises(PostAlreadyLiked)
    @deal.chain(deal.offline, deal.silent)
    def like(self, user: str) -> None:
        if user in self.likes:
            raise PostAlreadyLiked
        self.likes.add(user)

    @deal.post(lambda result: 'visits' in result)
    @deal.post(lambda result: 'likes' in result)
    @deal.post(lambda result: result['likes'] > 0)
    @deal.pure
    def get_state(self):
        return dict(visits=self.visits, likes=len(self.likes))
```

Now, Deal controls conditions and states of the object at runtime:

1. `@deal.inv` controls that visits count in post always non-negative.
1. `@deal.pre` checks user name format. We assume that it should be validated somewhere before by some nice forms with user-friendly error messages. So, if we have invalid login passed here, it's definitely developer's mistake.
1. `@deal.raises` says that only possible exception that can be raised is `PostAlreadyLiked`.
1. `@deal.chain(deal.offline, deal.silent)` controls that function has no network requests and has no output in stderr or stdout. So, if we are making unexpected network requests somewhere inside, deal let us know about it.
1. `deal.post` checks result format for `get_state`. So, all external code can be sure that fields `likes` and `visits` always represented in the result and likes always positive.

If code violates some condition, sub-exception of `deal.ContractError` will be raised:

```python
p = Post()
p.visits = -1
# InvContractError:
```

Dive deeper on [deal.readthedocs.io](https://deal.readthedocs.io/).
