# Linter

Deal can do static checks for functions with contracts to catch trivial mistakes. Don't expect it to find much. Static analysis in dynamic language is hard but deal tries its best to help you. Add the linter on your CI and it will help you to find bugs.

## flake8

Most probably, you already use [flake8](http://flake8.pycqa.org), so this option should suit best for you. Deal has built-in flake8 plugin which will be automatically discovered if you install flake8 and deal in the same environment.

```bash
python3 -m pip install --user flake8 deal
python3 -m flake8
```

## Built-in CLI command

Another option is to use built-in CLI from deal: `python3 -m deal lint`. I has beautiful colored output by default. Use `--json` option to get a compact JSON output. Pipe output into [jq](https://stedolan.github.io/jq/) to beautify JSON.

Since this is ad-hoc solution, it has a bit more beautiful colored output.

![linter output](../../assets/linter.png)

## Codes

General:

| Code    | Message |
| ------- | ------- |
| DEL001  | do not use `from deal import ...`, use `import deal` instead |
| DEL002  | ensure contract must have `result` arg |

Contracts:

| Code    | Message                   |
| ------- | ------------------------- |
| DEL011  | pre contract error        |
| DEL012  | post contract error       |
| DEL013  | example violates contract |
| DEL021  | raises contract error     |
| DEL031  | assert error              |

Markers:

| Code    | Message                 |
| ------- | ----------------------- |
| DEL041  | missed marker (global)  |
| DEL042  | missed marker (import)  |
| DEL043  | missed marker (io)      |
| DEL044  | missed marker (read)    |
| DEL045  | missed marker (write)   |
| DEL046  | missed marker (stdout)  |
| DEL047  | missed marker (stderr)  |
| DEL048  | missed marker (network) |
| DEL049  | missed marker (stdin)   |
| DEL050  | missed marker (syscall) |
| DEL055  | missed marker (random)  |
| DEL056  | missed marker (time)    |

## Partial execution

To check `pre` and `post` contracts, linter can partially execute them. For example:

```python run
import deal

@deal.post(lambda r: r != 0)
def f():
    return 0
```

Try to run linter against the code above:

```bash
$ python3 -m deal lint tmp.py
tmp.py
  6:11 DEL012  post contract error (0)
    return 0
```

Hence there are some rules to make your contracts linter-friendly:

+ Avoid side-effects, even logging.
+ Avoid external dependencies (functions and contants defined outside of the contract).
+ Keep them as small as possible. If you have a few different things to check, make separate contracts.

Linter silently ignores contract if it cannot be executed.
