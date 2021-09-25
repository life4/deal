# Documentation

## Sphinx autodoc

Deal has an integration with [sphinx] documentation generator, namely with [autodoc] extension. The integration includes all contracts for documented functions into the generated documentation.

[sphinx]: https://www.sphinx-doc.org/en/master/
[autodoc]: https://www.sphinx-doc.org/en/master/usage/extensions/autodoc.html

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

See also {ref}`details/examples:sphinx` example.

## Writing docstrings

The [Writing docstrings](https://sphinx-rtd-tutorial.readthedocs.io/en/latest/docstrings.html) page of Sphinx documentation provides a good description on how to write docstrings in [RST format](https://devguide.python.org/documenting/). Also, there is [PEP-257](https://www.python.org/dev/peps/pep-0257/) which describes stylistic conventions related to docstrings (and tells what docstrings are).

## Using Markdown

If you prefer more human-friendly [Markdown](https://en.wikipedia.org/wiki/Markdown), it needs a bit of hacking. The [MyST-Parser](https://github.com/executablebooks/MyST-Parser) extension allows to use Markdown for Sphinx documentation but not for docstrings (see [#228](https://github.com/executablebooks/MyST-Parser/issues/228)). If you want Markdown support for docstrings, you can add [m2r2](https://github.com/CrossNox/m2r2) converter into `docs/conf.py` as a hook for autodoc:

```python
from m2r2 import convert

def autodoc_process(app, what, name, obj, options, lines):
    if not lines:
        return lines
    text = convert('\n'.join(lines))
    lines[:] = text.split('\n')

def setup(app):
    app.connect('autodoc-process-docstring', autodoc_process)
```

It doesn't matter what format you choose, deal supports all of them.
