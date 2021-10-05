# Examples

## choice

```{eval-rst}
.. literalinclude:: ../../examples/choice.py
```

## concat

```{eval-rst}
.. literalinclude:: ../../examples/concat.py
```

## count

```{eval-rst}
.. literalinclude:: ../../examples/count.py
```

## div

```{eval-rst}
.. literalinclude:: ../../examples/div.py
```

## fuzzing_atheris

```{eval-rst}
.. literalinclude:: ../../examples/fuzzing_atheris.py
```

## fuzzing_pythonfuzz

```{eval-rst}
.. literalinclude:: ../../examples/fuzzing_pythonfuzz.py
```

## using_hypothesis

```{eval-rst}
.. literalinclude:: ../../examples/using_hypothesis.py
```

## index_of

```{eval-rst}
.. literalinclude:: ../../examples/index_of.py
```

## min

```{eval-rst}
.. literalinclude:: ../../examples/min.py
```

Linter output:

```bash
$ python3 -m deal lint examples/min.py
examples/min.py
  21:4 DEAL011 pre contract error ([])
    my_min([])
    ^
```

## format

```{eval-rst}
.. literalinclude:: ../../examples/format.py
```

Linter output:

```bash
$ python3 -m deal lint examples/format.py
examples/format.py
  32:10 DEAL011 expected 1 argument(s) but 0 found ('{:s}')
    print(format('{:s}'))               # not enough args
          ^
  33:10 DEAL011 expected 1 argument(s) but 2 found ('{:s}', 'a', 'b')
    print(format('{:s}', 'a', 'b'))     # too many args
          ^
  34:10 DEAL011 expected float, str given ('{:d}', 'a')
    print(format('{:d}', 'a'))          # bad type
          ^
```

## sphinx

Source code:

```{eval-rst}
.. literalinclude:: ../../examples/sphinx.py
```

Sphinx config (`docs/conf.py`):

```python run
import deal

extensions = ['sphinx.ext.autodoc']

def setup(app):
    deal.autodoc(app)
```

Including into a documentation page (`docs/index.rst`):

```rst
.. autofunction:: examples.sphinx.example
```

Generated output:

```{eval-rst}
.. autofunction:: examples.sphinx.example
```
