# Documentation

## Sphinx autodoc

Deal has an integration with [sphinx] documentation generator, namely with [autodoc] extension. The integration includes all contracts for documented functions into the generated documentation.

[sphinx]: https://www.sphinx-doc.org/en/master/
[autodoc]: https://www.sphinx-doc.org/en/master/usage/extensions/autodoc.html

The minimal config:

```python run
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

## deal.example

The decorator {py:func}`deal.example` allows to provide a usage example for the decorated function. This example is executed only when running [tests](../basic/tests) and partially checked by the linter. It's not, however, executed at runtime. The example must return `True` if it is valid.

```python run
@deal.example(lambda: double(3) == 6)
def double(x):
    return x * 2
```

Depending on the context and on the mypy version you use, you may encounter `Cannot determine type of "double"` error message from mypy (see [mypy#11212]). If you do, you can:

1. Upgrade mypy version above 0.910.
1. Add `# type: ignore[has-type]` to the reported line.
1. Add [has-type] code into [disable_error_code] list in the [mypy configuration file][mypy-config].

[mypy#11212]: https://github.com/python/mypy/issues/11212
[has-type]: https://mypy.readthedocs.io/en/stable/error_code_list.html#check-that-type-of-target-is-known-has-type
[disable_error_code]: https://mypy.readthedocs.io/en/stable/config_file.html#confval-disable_error_code
[mypy-config]: https://mypy.readthedocs.io/en/stable/config_file.html

If you want to provide an example of when the function raises an exception, you can catch and compare this exception using {py:func}`deal.catch`:

```python run
@deal.example(lambda: deal.catch(div, 4, 0) is ZeroDivisionError)
@deal.raises(ZeroDivisionError)
@deal.reason(ZeroDivisionError, lambda x: x == 0)
def div(x, y):
    return x / y
```

For more complex examples (requiring setup, teardown, or complicated arguments) use [doctest](https://docs.python.org/3/library/doctest.html).

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
