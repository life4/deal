# Linter

Deal can do static checks for functions with contracts to catch trivial mistakes. Don't expect it to find much. Static analysis in dynamic language is hard but deal tries its best to help you. Add the linter on your CI and it will help you to find bugs.

## flake8

Most probably, you already use [flake8](http://flake8.pycqa.org), so this option should suit best for you. Deal has built-in flake8 plugin which will be autimatically discovered if you install flake8 and deal in the same environment.

```bash
python3 -m pip install --user flake8 deal
python3 -m flake8
```

## FlakeHell

[FlakeHell](https://github.com/life4/flakehell) is a wrapper around Flake8 to get rid of legacy and improve some things like configuration. Deal usage with FlakeHell is almost the same as with Flake8 except that all plugins must be explicitly specified in the `pyproject.toml` config:

```toml
[tool.flakehell.plugins]
deal = ["+*"]
```

## Built-in CLI command

Another option is to use built-in CLI from deal: `python3 -m deal lint`. I has beautiful colored output by default. Use `--json` option to get a compact JSON output. Pipe output into [jq](https://stedolan.github.io/jq/) to beautify JSON.

Since this is ad-hoc solution, it has a bit more beautiful colored output.

![linter output](../../assets/linter.png)

## Codes

General:

```eval_rst
+---------+--------------------------------------------------------------+
| Code    | Message                                                      |
+=========+==============================================================+
| DEAL001 | do not use `from deal import ...`, use `import deal` instead |
+---------+--------------------------------------------------------------+
```

Contracts:

```eval_rst
+---------+-----------------------+
| Code    | Message               |
+=========+=======================+
| DEAL011 | pre contract error    |
+---------+-----------------------+
| DEAL012 | post contract error   |
+---------+-----------------------+
| DEAL021 | raises contract error |
+---------+-----------------------+
| DEAL031 | assert error          |
+---------+-----------------------+
```

Markers:

```eval_rst
+---------+-------------------------+
| Code    | Message                 |
+=========+=========================+
| DEAL041 | missed marker (global)  |
+---------+-------------------------+
| DEAL042 | missed marker (import)  |
+---------+-------------------------+
| DEAL043 | missed marker (io)      |
+---------+-------------------------+
| DEAL044 | missed marker (read)    |
+---------+-------------------------+
| DEAL045 | missed marker (write)   |
+---------+-------------------------+
| DEAL046 | missed marker (stdout)  |
+---------+-------------------------+
| DEAL047 | missed marker (stderr)  |
+---------+-------------------------+
| DEAL048 | missed marker (network) |
+---------+-------------------------+
```
