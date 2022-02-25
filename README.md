# ![Deal](https://raw.githubusercontent.com/life4/deal/master/logo.png)

[![Build Status](https://cloud.drone.io/api/badges/life4/deal/status.svg)](https://cloud.drone.io/life4/deal)
[![PyPI version](https://img.shields.io/pypi/v/deal.svg)](https://pypi.python.org/pypi/deal)
[![Development Status](https://img.shields.io/pypi/status/deal.svg)](https://pypi.python.org/pypi/deal)

A Python library for [design by contract](https://en.wikipedia.org/wiki/Design_by_contract) (DbC) and checking values, exceptions, and side-effects. In a nutshell, deal empowers you to write bug-free code. By adding a few decorators to your code, you get for free tests, static analysis, formal verification, and much more. Read [intro](https://deal.readthedocs.io/basic/intro.html) to get started.

## Features

* [Classic DbC: precondition, postcondition, invariant.][values]
* [Tracking exceptions and side-effects.][exceptions]
* [Property-based testing.][tests]
* [Static checker.][linter]
* Integration with pytest, flake8, sphinx, and hypothesis.
* Type annotations support.
* [External validators support.][validators]
* [Contracts for importing modules.][module_load]
* [Can be enabled or disabled on production.][runtime]
* [Colorless][colorless]: annotate only what you want. Hence, easy integration into an existing project.
* Colorful: syntax highlighting for every piece of code in every command.
* [Memory leaks detection][leaks]: deal makes sure that pure functions don't leave unexpected objects in the memory.
* DRY: test discovery, error messages generation.
* Partial execution: linter executes contracts to statically check possible values.
* [Formal verification][verification]: prove that your code works for all input (or find out when it doesn't).
* Fast: each code change is benchmarked and profiled.
* Reliable: the library has 100% test coverage, partially verified, and runs on production by multiple companies since 2018.

[values]: https://deal.readthedocs.io/basic/values.html
[exceptions]: https://deal.readthedocs.io/basic/exceptions.html
[tests]: https://deal.readthedocs.io/basic/tests.html
[linter]: https://deal.readthedocs.io/basic/linter.html
[validators]: https://deal.readthedocs.io/details/contracts.html#external-validators
[module_load]: https://deal.readthedocs.io/details/module_load.html
[runtime]: https://deal.readthedocs.io/basic/runtime.html
[colorless]: http://journal.stuffwithstuff.com/2015/02/01/what-color-is-your-function/
[leaks]: https://deal.readthedocs.io/basic/tests.html#memory-leaks
[verification]: https://deal.readthedocs.io/basic/verification.html

## Deal in 30 seconds

```python
# the result is always non-negative
@deal.post(lambda result: result >= 0)
# the function has no side-effects
@deal.pure
def count(items: List[str], item: str) -> int:
    return items.count(item)

# generate test function
test_count = deal.cases(count)
```

Now we can:

* Run `python3 -m deal lint` or `flake8` to statically check errors.
* Run `python3 -m deal test` or `pytest` to generate and run tests.
* Just use the function in the project and check errors in runtime.

Read more in the [documentation](https://deal.readthedocs.io/).

## Installation

```bash
python3 -m pip install --user 'deal[all]'
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
