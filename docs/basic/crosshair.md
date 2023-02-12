# CrossHair

```{warning}
CrossHair is an **experimental** tool and it runs your code. So, use it only with safe functions, don't run it on the code that may wipe out your system or do bank transactions.
```

[CrossHair](https://github.com/pschanely/CrossHair) is a third-party tool for finding bugs in Python code with deal support. It is a verifier-driven fuzzer (also known as "[concolic testing](https://en.wikipedia.org/wiki/Concolic_testing)"), something in between deal {doc}`/basic/tests` and {doc}`/basic/verification`. It calls the given function multiple times but instead of actual values it passes special mocks, allowing it explore different execution branches.

Installation:

```bash
python3 -m pip install --user crosshair-tool
```

Usage:

```bash
python3 -m crosshair watch ./examples/div.py
```

```{note}
CrossHair is a third-party tool. We're not responsible for bugs in this integration. Use CrossHair [issue tracker](https://github.com/pschanely/CrossHair/issues) for all issues you encounter.
```

Further reading:

+ [CrossHair documentation](https://crosshair.readthedocs.io/en/latest/introduction.html)
+ [Deal Support](https://crosshair.readthedocs.io/en/latest/kinds_of_contracts.html#deal-support)
+ [How Does It Work?](https://crosshair.readthedocs.io/en/latest/how_does_it_work.html)
