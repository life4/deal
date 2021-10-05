# Stubs

When [linter](../basic/linter) analyses a function, it checks all called functions inside it, even if these functions have no explicit contracts. For example:

```python run
import deal

def a():
    raise ValueError

@deal.raises(NameError)
def b():
    return a()
```

Here deal finds and error:

```bash
$ python3 -m deal lint tmp.py
tmp.py
  8:11 raises contract error (ValueError)
    return a()
```

However, in the next case deal doesn't report anything:

```python run
import deal

def a():
    raise ValueError

def b():
    return a()

@deal.raises(NameError)
def c():
    return b()
```

That's because the exception is raised deep inside the call chain. Analyzing function calls too deep would make deal too slow. The solution is to make contracts for everything in your code that you want to be analyzed. However, when it's about third-party libraries where you can't modify the code, stubs come into play.

Use `stub` command to generate stubs for a Python file:

```bash
python3 -m deal stub /path/to/a/file.py
```

The command above will produce `/path/to/a/file.json` stub. On the next runs linter will use it do detect contracts.

## Built-in stubs

Deal comes with a few pre-generated stubs that are automatically used by the linter:

+ Standard library (CPython 3.7)
+ [marshmallow](https://pypi.org/project/marshmallow/)
+ [python-dateutil](https://pypi.org/project/python-dateutil/)
+ [pytz](https://pypi.org/project/pytz/)
+ [requests](https://pypi.org/project/requests/)
+ [urllib3](https://pypi.org/project/urllib3/)
