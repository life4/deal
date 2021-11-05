# API

## Values

```{eval-rst}
.. autofunction:: deal.pre
.. autofunction:: deal.post
.. autofunction:: deal.ensure
.. autofunction:: deal.inv
.. autofunction:: deal.example
.. autofunction:: deal.dispatch
```

## Side-effects and exceptions

```{eval-rst}
.. autofunction:: deal.has
.. autofunction:: deal.raises
.. autofunction:: deal.reason
```

## Helpers

```{eval-rst}
.. autofunction:: deal.inherit
.. autofunction:: deal.chain
.. autofunction:: deal.pure
.. autofunction:: deal.safe
.. autofunction:: deal.implies
.. autofunction:: deal.catch
```

## Testing

Keep in mind that sphinx [skipped some of the docstrings](https://github.com/sphinx-doc/sphinx/issues/7787) for `deal.cases`.

```{eval-rst}
.. autoclass:: deal.cases
    :members:
    :special-members:

.. autoclass:: deal.TestCase
    :members:
```

## Introspection

```{eval-rst}
.. automodule:: deal.introspection
```

## State management

```{eval-rst}
.. autofunction:: deal.disable
.. autofunction:: deal.enable
.. autofunction:: deal.reset
```

## Other functions

```{eval-rst}
.. autofunction:: deal.autodoc
.. autofunction:: deal.activate
.. autofunction:: deal.module_load
```

## Exceptions

```{eval-rst}
.. autoexception:: deal.ContractError
.. autoexception:: deal.ExampleContractError
.. autoexception:: deal.InvContractError
.. autoexception:: deal.MarkerError
.. autoexception:: deal.NoMatchError
.. autoexception:: deal.OfflineContractError
.. autoexception:: deal.PostContractError
.. autoexception:: deal.PreContractError
.. autoexception:: deal.RaisesContractError
.. autoexception:: deal.ReasonContractError
.. autoexception:: deal.SilentContractError
```
