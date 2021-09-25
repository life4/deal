# API

## Values

```{eval-rst}
.. autofunction:: deal.pre
.. autofunction:: deal.post
.. autofunction:: deal.ensure
.. autofunction:: deal.inv
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
.. autofunction:: deal.chain
.. autofunction:: deal.pure
.. autofunction:: deal.safe
.. autofunction:: deal.implies
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

## Other

```{eval-rst}
.. autofunction:: deal.module_load
.. autofunction:: deal.disable
.. autofunction:: deal.enable
.. autofunction:: deal.reset
```
