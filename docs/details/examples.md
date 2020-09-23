# Examples

## choice

```eval_rst
.. literalinclude:: ../../examples/choice.py
```

## concat

```eval_rst
.. literalinclude:: ../../examples/concat.py
```

## count

```eval_rst
.. literalinclude:: ../../examples/count.py
```

## div

```eval_rst
.. literalinclude:: ../../examples/div.py
```

## index_of

```eval_rst
.. literalinclude:: ../../examples/index_of.py
```

## format

```eval_rst
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
