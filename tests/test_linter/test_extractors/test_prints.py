# built-in
import ast

# external
import astroid
import pytest

# project
from deal.linter._extractors import get_prints


@pytest.mark.parametrize('text, expected', [
    ('print(1)', ('print', )),
    ('sys.stdout.write(1)', ('sys.stdout', )),
    ('open("fpath", "w")', ('open', )),
    ('open("fpath", mode="w")', ('open', )),
    ('with open("fpath", "w") as f: ...', ('open', )),
    ('with something: ...', ()),
    ('open("fpath", "r")', ()),
    ('open("fpath")', ()),
    ('open("fpath", encoding="utf8")', ()),
])
def test_get_prints_simple(text, expected):
    tree = astroid.parse(text)
    print(tree.repr_tree())
    returns = tuple(r.value for r in get_prints(body=tree.body))
    assert returns == expected

    tree = ast.parse(text)
    print(ast.dump(tree))
    returns = tuple(r.value for r in get_prints(body=tree.body))
    assert returns == expected


@pytest.mark.parametrize('text, expected', [
    ('from pathlib import Path\np = Path()\np.write_text("lol")', ('Path.open', )),
    ('from pathlib import Path\np = Path()\np.open("w")', ('Path.open', )),
    ('from pathlib import Path\np = Path()\nwith p.open("w"): ...', ('Path.open', )),
    ('from pathlib import Path\np = Path()\np.read_text()', ()),
    ('from pathlib import Path\np = Path()\np.open()', ()),
    ('with something.open("w"): ...', ()),
    ('something = file\nwith something.open("w"): ...', ()),
])
def test_get_prints_infer(text, expected):
    tree = astroid.parse(text)
    print(tree.repr_tree())
    returns = tuple(r.value for r in get_prints(body=tree.body))
    assert returns == expected
