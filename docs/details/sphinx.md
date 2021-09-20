# Sphinx

Deal has an integration with [sphinx] documentation generator, namely with [autodoc] extension. The integration includes all contracts for documented functions into the generated documentation.

The minimal config:

```python
import deal

extensions = ['sphinx.ext.autodoc']

def setup(app):
    deal.autodoc(app)
```

And that's all. Now, every time you include something using autodoc, deal will automatically inject documentation for contracts.

This is how deal converts every contract into text:

1. If the contract has `message` argument specified, it is used.
1. If the contract is a named function, the function name is used.
1. If the contract is a lambda, the source code is used.

See also [sphinx](./examples.html#sphinx) example.

[sphinx]: https://www.sphinx-doc.org/en/master/
[autodoc]: https://www.sphinx-doc.org/en/master/usage/extensions/autodoc.html
