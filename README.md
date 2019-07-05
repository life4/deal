# ![Deal](https://raw.githubusercontent.com/orsinium/deal/master/logo.png)

[![Build Status](https://travis-ci.org/orsinium/deal.svg?branch=master)](https://travis-ci.org/orsinium/deal) [![Coverage Status](https://coveralls.io/repos/github/orsinium/deal/badge.svg)](https://coveralls.io/github/orsinium/deal) [![PyPI version](https://img.shields.io/pypi/v/deal.svg)](https://pypi.python.org/pypi/deal) [![Development Status](https://img.shields.io/pypi/status/deal.svg)](https://pypi.python.org/pypi/deal) [![Code size](https://img.shields.io/github/languages/code-size/orsinium/deal.svg)](https://github.com/orsinium/deal) [![License](https://img.shields.io/pypi/l/deal.svg)](LICENSE)

**Deal** -- python library for [design by contract](https://en.wikipedia.org/wiki/Design_by_contract) (DbC) programming.

That's nice `assert` statements in decorators style to validate function input, output, available operations and object state. Goal is make testing much easier and detect errors in your code that occasionally was missed in tests.

## Features

* Functional declaration.
* Custom exceptions.
* Raising exceptions from contract.
* Django Forms styled validators.
* Attribute setting invariant validation.
* Dynamically assigned attributes and methods invariant validation.
* Decorators to control available resources: forbid input/output, network operations, raising exceptions

## Available decorators

## Installation

```bash
pip3 install --user deal
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

    @deal.pre(lambda user: REX_LOGIN.match(user), 'invalid username format')
    @deal.raises(PostAlreadyLiked)
    @deal.chain(deal.offline, deal.silent)
    def like(self, user: str) -> None:
        if user in self.likes:
            raise PostAlreadyLiked
        likes.add(user)

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
