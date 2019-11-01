# Static analysis

Deal can do static checks for functions with contracts to catch trivial mistakes. Use [flake8](http://flake8.pycqa.org) or [flakehell](https://github.com/life4/flakehell) to run it.

![](../assets/linter.png)

## Codes

| Code    | Message               |
| ------- | --------------------- |
| DEAL001 | do not use `from deal import ...`, use `import deal` instead |
| DEAL011 | post contract error   |
| DEAL012 | raises contract error |
| DEAL013 | silent contract error |
