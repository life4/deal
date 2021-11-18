# References

This page provides a quick navigation by the documentation in case if you're looking for something specific.

## Decorators

| decorator        | reference                | documentation |
| ---------------- | ------------------------ | ------------- |
| `@deal.chain`    | {py:func}`deal.chain`    | {doc}`/details/contracts` / {ref}`details/contracts:deal.chain` |
| `@deal.dispatch` | {py:func}`deal.dispatch` | {doc}`/details/dispatch` |
| `@deal.ensure`   | {py:func}`deal.ensure`   | {doc}`/basic/values` / {ref}`basic/values:deal.ensure` |
| `@deal.example`  | {py:func}`deal.example`  | {doc}`/details/docs` / {ref}`details/docs:deal.example` |
| `@deal.has`      | {py:func}`deal.has`      | {doc}`/basic/side-effects` |
| `@deal.inherit`  | {py:func}`deal.inherit`  | {doc}`/details/contracts` / {ref}`details/contracts:deal.inherit` |
| `@deal.inv`      | {py:func}`deal.inv`      | {doc}`/basic/values` / {ref}`basic/values:deal.inv` |
| `@deal.post`     | {py:func}`deal.post`     | {doc}`/basic/values` / {ref}`basic/values:deal.post` |
| `@deal.pre`      | {py:func}`deal.pre`      | {doc}`/basic/values` / {ref}`basic/values:deal.pre` |
| `@deal.pure`     | {py:func}`deal.pure`     | -- |
| `@deal.raises`   | {py:func}`deal.raises`   | {doc}`/basic/exceptions` / {ref}`basic/exceptions:deal.raises` |
| `@deal.reason`   | {py:func}`deal.reason`   | {doc}`/basic/exceptions` / {ref}`basic/exceptions:deal.reason` |
| `@deal.safe`     | {py:func}`deal.safe`     | -- |

## Functions

| decorator          | reference                | documentation |
| ------------------ | ------------------------ | ------------- |
| `deal.activate`    | {py:func}`deal.activate` | {doc}`/details/module_load` |
| `deal.autodoc`     | {py:func}`deal.autodoc`  | {doc}`/details/docs` / {ref}`details/docs:sphinx autodoc` |
| `deal.cases`       | {py:class}`deal.cases`   | {doc}`/basic/tests` |
| `deal.catch`       | {py:func}`deal.catch`    | {doc}`/details/docs` / {ref}`details/docs:deal.example` |
| `deal.disable`     | {py:func}`deal.disable`  | {doc}`/basic/runtime` / {ref}`basic/runtime:contracts on production` |
| `deal.enable`      | {py:func}`deal.enable`   | {doc}`/basic/runtime` / {ref}`basic/runtime:contracts on production` |
| `deal.implies`     | {py:func}`deal.implies`  | -- |
| `deal.module_load` | {py:func}`deal.module_load` | {doc}`/details/module_load` |
| `deal.reset`       | {py:func}`deal.reset`    | {doc}`/basic/runtime` / {ref}`basic/runtime:contracts on production` |

## Exceptions

| decorator                   | reference                           | documentation |
| --------------------------- | ----------------------------------- | ------------- |
| `deal.ContractError`        | {py:exc}`deal.ContractError`        | {doc}`/basic/values` / {ref}`basic/values:exceptions` |
| `deal.ExampleContractError` | {py:exc}`deal.ExampleContractError` | -- |
| `deal.InvContractError`     | {py:exc}`deal.InvContractError`     | {doc}`/basic/values` / {ref}`basic/values:exceptions` |
| `deal.MarkerError`          | {py:exc}`deal.MarkerError`          | -- |
| `deal.NoMatchError`         | {py:exc}`deal.NoMatchError`         | {doc}`/details/dispatch` |
| `deal.OfflineContractError` | {py:exc}`deal.OfflineContractError` | -- |
| `deal.PostContractError`    | {py:exc}`deal.PostContractError`    | {doc}`/basic/values` / {ref}`basic/values:exceptions` |
| `deal.PreContractError`     | {py:exc}`deal.PreContractError`     | {doc}`/basic/values` / {ref}`basic/values:exceptions` |
| `deal.RaisesContractError`  | {py:exc}`deal.RaisesContractError`  | -- |
| `deal.ReasonContractError`  | {py:exc}`deal.ReasonContractError`  | -- |
| `deal.SilentContractError`  | {py:exc}`deal.SilentContractError`  | -- |

## CLI commands

| command    | reference                   | documentation |
| ---------- | --------------------------- | ------------- |
| `decorate` | {ref}`details/cli:decorate` | {doc}`/details/contracts` / {ref}`details/contracts:generating contracts` |
| `lint`     | {ref}`details/cli:lint`     | {doc}`/basic/linter` / {ref}`basic/linter:built-in cli command` |
| `memtest`  | {ref}`details/cli:memtest`  | {doc}`/details/tests` / {ref}`details/tests:finding memory leaks` |
| `prove`    | {ref}`details/cli:prove`    | {doc}`/basic/verification` |
| `stub`     | {ref}`details/cli:stub`     | {doc}`/details/stubs` |
| `test`     | {ref}`details/cli:test`     | {doc}`/basic/tests` / {ref}`basic/tests:cli` |

## Integrations

| tool       | github           | integration docs |
| ---------  | ---------------- | ---------------- |
| atheris    | [google/atheris](https://github.com/google/atheris) | {doc}`/details/tests` / {ref}`details/tests:fuzzing`
| flake8     | [PyCQA/flake8](https://github.com/PyCQA/flake8) | {doc}`/basic/linter` / {ref}`basic/linter:flake8` |
| hypothesis | [HypothesisWorks/hypothesis](https://github.com/HypothesisWorks/hypothesis) | {doc}`/details/tests` / {ref}`details/tests:custom strategies` |
| mypy       | [python/mypy](https://github.com/python/mypy) | {doc}`/details/contracts` / {ref}`details/contracts:typing` |
| pytest     | [pytest-dev/pytest](https://github.com/pytest-dev/pytest) | {doc}`/basic/tests`  |
| sphinx     | [sphinx-doc/sphinx](https://github.com/sphinx-doc/sphinx) | {doc}`/details/docs` / {ref}`details/docs:sphinx autodoc` |

## Articles

+ [Make tests a part of your app](https://dev.to/sobolevn/make-tests-a-part-of-your-app-8nm)

## Projects integrating deal

+ [CrossHair](https://github.com/pschanely/CrossHair)
+ [flake8-functions-names](https://github.com/Melevir/flake8-functions-names)
