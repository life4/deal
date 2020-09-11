# ![Deal](https://raw.githubusercontent.com/life4/deal/master/logo.png)

[![Build Status](https://travis-ci.org/life4/deal.svg?branch=master)](https://travis-ci.org/life4/deal)
[![Coverage Status](https://coveralls.io/repos/github/life4/deal/badge.svg)](https://coveralls.io/github/life4/deal)
[![PyPI version](https://img.shields.io/pypi/v/deal.svg)](https://pypi.python.org/pypi/deal)
[![Development Status](https://img.shields.io/pypi/status/deal.svg)](https://pypi.python.org/pypi/deal)

**Deal** -- python library for [design by contract](https://en.wikipedia.org/wiki/Design_by_contract) (DbC) and checking values, exceptions, and side-effects. Read [intro](https://deal.readthedocs.io/basic/intro.html) to get started.

## Features

* [Classic DbC: precondition, postcondition, invariant.][values]
* [Tracking exceptions and side-effects.][exceptions]
* [Property-based testing.][tests]
* [Static checker.][linter]
* Integration with pytest and flake8.
* Type annotations support.
* [External validators support.][validators]
* [Contracts for importing modules.][module_load]
* [Can be enabled or disabled on production.][runtime]

[values]: https://deal.readthedocs.io/basic/values.html
[exceptions]: https://deal.readthedocs.io/basic/exceptions.html
[tests]: https://deal.readthedocs.io/basic/tests.html
[linter]: https://deal.readthedocs.io/basic/linter.html
[validators]: https://deal.readthedocs.io/details/validators.html
[module_load]: https://deal.readthedocs.io/details/module_load.html
[runtime]: https://deal.readthedocs.io/basic/runtime.html

## Deal in 30 seconds

```python
# the result is always non-negative
@deal.post(lambda result: result >= 0)
# the function has no side-effects
@deal.has()
def count(items: List[str], item: str) -> int:
    return items.count(item)

# test case
@pytest.mark.parametrize('case', deal.cases(count))
def test_count(case: deal.TestCase):
    case()
```

Now we can:

* Run `python3 -m deal lint` or `flake8` to statically check errors.
* Run `python3 -m deal test` or `pytest` to generate and run tests.
* Just use the function in the project and check errors in runtime.

Read mor in the [documentation](https://deal.readthedocs.io/).

## Installation

```bash
python3 -m pip install --user deal
```

## Contributing

Contributions are welcome! A few ideas what you can contribute:

* Add new checks for the linter.
* Improve documentation.
* Add more tests.
* Improve performance.
* Found a bug? Fix it!
* Made an article about deal? Great! Let's add it into the `README.md`.
* Don't have time to code? No worries! Just tell your friends and subscribers about the project. More users -> more contributors -> more cool features.

Thank you :heart:
