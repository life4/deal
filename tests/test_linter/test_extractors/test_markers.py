# built-in
import ast

# external
import astroid
import pytest

# project
from deal.linter._extractors import get_markers


@pytest.mark.parametrize('text, expected', [
    ('print(1)', ('stdout', )),
    ('print(1, file=sys.stdout)', ('stdout', )),
    ('print(1, file=sys.stderr)', ('stderr', )),
    ('print(1, file=stream)', ()),

    ('import sys\nsys.stdout.write(1)', ('stdout', )),
    ('import sys\nsys.stderr.write(1)', ('stderr', )),

    ('open("fpath", "w")', ('write', )),
    ('open("fpath", mode="w")', ('write', )),
    ('with open("fpath", "w") as f: ...', ('write', )),

    ('with something: ...', ()),

    ('with open("fpath") as f: ...', ('read', )),
    ('with open("fpath", "r") as f: ...', ('read', )),
    ('with open("fpath", mode="r") as f: ...', ('read', )),
    ('open("fpath", "r")', ('read', )),
    ('open("fpath")', ('read', )),
    ('open("fpath", encoding="utf8")', ('read', )),
])
def test_get_markers_simple(text, expected):
    tree = astroid.parse(text)
    print(tree.repr_tree())
    tokens = list(get_markers(body=tree.body))
    markers = tuple(t.marker for t in tokens if t.marker != 'import')
    assert markers == expected

    tree = ast.parse(text)
    print(ast.dump(tree))
    tokens = list(get_markers(body=tree.body))
    markers = tuple(t.marker for t in tokens if t.marker != 'import')
    assert markers == expected


@pytest.mark.parametrize('text, expected', [
    ('from pathlib import Path\np = Path()\np.write_text("lol")', ('Path.open', )),
    ('from pathlib import Path\np = Path()\np.open("w")', ('Path.open', )),
    ('from pathlib import Path\np = Path()\nwith p.open("w"): ...', ('Path.open', )),

    ('from pathlib import Path\np = Path()\np.open("r")', ()),          # allowed mode
    ('from pathlib import Path\np = Path()\np.open(mode="r")', ()),     # allowed mode
    ('from pathlib import Path\np = Path()\np.read_text()', ()),    # read, not write
    ('from pathlib import Path\np = Path()\np.open()', ()),         # implicit read
    ('with something.open("w"): ...', ()),                          # not pathlib
    ('something = file\nwith something.open("w"): ...', ()),        # not pathlib
    ('class Path:\n def write_text(): pass\np = Path()\np.write_text()', ()),   # not pathlib
])
def test_get_markers_infer(text, expected):
    tree = astroid.parse(text)
    print(tree.repr_tree())
    tokens = list(get_markers(body=tree.body))
    for token in tokens:
        assert token.marker in ('read', 'write', 'stdout', 'stderr', 'import')
    values = tuple(t.value for t in tokens if t.marker != 'import')
    assert values == expected


@pytest.mark.parametrize('text, expected', [
    ('global a', ('global', )),
    ('global a, b, c', ('global', )),

    ('nonlocal a', ('global', )),
    ('nonlocal a, b, c', ('global', )),

    ('import a', ('import', )),
    ('import a as b', ('import', )),
    ('import a as b, c', ('import', )),

    ('from a import b', ('import', )),
    ('from a import b as c', ('import', )),
])
def test_get_globals_simple(text, expected):
    tree = astroid.parse(text)
    print(tree.repr_tree())
    tokens = list(get_markers(body=tree.body))
    markers = tuple(t.marker for t in tokens)
    assert markers == expected

    tree = ast.parse(text)
    print(ast.dump(tree))
    tokens = list(get_markers(body=tree.body))
    markers = tuple(t.marker for t in tokens)
    assert markers == expected
