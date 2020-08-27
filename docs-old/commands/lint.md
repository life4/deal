# **lint**: run static analysis

Deal can do static checks for functions with contracts to catch trivial mistakes. Use [flake8](http://flake8.pycqa.org) or [flakehell](https://github.com/life4/flakehell) to run it.

Another option is to use built-in CLI from deal: `python3 -m deal lint`. I has beautiful colored output by default. Use `--json` option to get compact JSON output. Pipe output into [jq](https://stedolan.github.io/jq/) to beautify JSON.

![linter output](../../assets/linter.png)

## Codes

| Code    | Message                                                      |
| ------- | ------------------------------------------------------------ |
| DEAL001 | do not use `from deal import ...`, use `import deal` instead |
| DEAL011 | pre contract error                                           |
| DEAL012 | post contract error                                          |
| DEAL021 | raises contract error                                        |
| DEAL022 | silent contract error                                        |
| DEAL023 | pure contract error                                          |
| DEAL031 | assert error                                                 |
