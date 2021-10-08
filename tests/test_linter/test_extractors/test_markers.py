import ast
from textwrap import dedent

import astroid
import pytest

from deal.linter._extractors import get_markers
from deal.linter._stub import StubsManager


@pytest.mark.parametrize('text, expected', [
    ('print(1)', ('stdout', )),
    ('print(1, sep=sys.stderr)', ('stdout', )),
    ('print(1, file=sys.stdout)', ('stdout', )),
    ('print(1, file=sys.stderr)', ('stderr', )),
    ('print(1, file=stream)', ()),

    ('import sys\nsys.stdout.write(1)', ('stdout', )),
    ('import sys\nsys.stderr.write(1)', ('stderr', )),

    ('open("fpath", "w")', ('write', )),
    ('open("fpath", mode="w")', ('write', )),
    ('with open("fpath", "w") as f: ...', ('write', )),

    ('with something: ...', ()),     # uninferrable `with` test
    ('something().anything()', ()),  # complex call, cannot get name

    ('with open("fpath") as f: ...', ('read', )),
    ('with open("fpath", "r") as f: ...', ('read', )),
    ('with open("fpath", mode="r") as f: ...', ('read', )),
    ('open("fpath", "r")', ('read', )),
    ('open("fpath")', ('read', )),
    ('open("fpath", encoding="utf8")', ('read', )),

    ('input()', ('stdin', )),
    ('input("say hi: ")', ('stdin', )),
    ('sys.stdin.read()', ('stdin', )),
    ('sys.stdin.read(10)', ('stdin', )),

    ('random.randint(10)', ('random', )),
    ('random.randrange(10)', ('random', )),
    ('random.random(10)', ('random', )),
    ('randrange(10)', ('random', )),

    ('os.system("echo")', ('syscall', )),
    ('os.execvp("echo", ["hi"])', ('syscall', )),
    ('subprocess.run("echo")', ('syscall', )),
    ('subprocess.call("echo")', ('syscall', )),
    ('subprocess.call(["echo"])', ('syscall', )),
    ('proc = subprocess.Popen("echo")', ('syscall', )),
    ('subprocess.SubprocessError()', ()),

    ('time.time()', ('time', )),
    ('time()', ('time', )),
    ('time_ns()', ('time', )),
    ('os.times()', ('time', )),
    ('datetime.now()', ('time', )),
    ('now()', ()),
])
def test_io_hardcoded(text, expected):
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
    ('from pathlib import Path\np = Path()\np.write_text("lol")', ('write', )),
    ('from pathlib import Path\np = Path()\np.open("w")', ('write', )),
    ('from pathlib import Path\np = Path()\nwith p.open("w"): ...', ('write', )),

    ('from pathlib import Path\np = Path()\np.open("r")', ()),          # allowed mode
    ('from pathlib import Path\np = Path()\np.open(mode="r")', ()),     # allowed mode
    ('from pathlib import Path\np = Path()\np.read_text()', ()),    # read, not write
    ('from pathlib import Path\np = Path()\np.open()', ()),         # implicit read

    # not pathlib
    ('with something.open("w"): ...', ()),
    ('something = file\nwith something.open("w"): ...', ()),
    ('class Path:\n def write_text(): pass\np = Path()\np.write_text()', ()),
    ('class Path:\n def write_text(): pass\nPath.write_text()', ()),
])
def test_io_infer(text, expected):
    tree = astroid.parse(text)
    print(tree.repr_tree())
    tokens = list(get_markers(body=tree.body))
    markers = tuple(t.marker for t in tokens if t.marker != 'import')
    assert markers == expected


@pytest.mark.parametrize('text, expected', [
    ('from random import choice \nchoice([1,2])', ('random', )),
    ('choice([1,2])', ()),
    ('choice = lambda:0 \nchoice()', ()),
    ('class A:\n def b(self): pass \nchoice = A().b \nchoice()', ()),
])
def test_other_infer(text, expected):
    tree = astroid.parse(text)
    print(tree.repr_tree())
    tokens = list(get_markers(body=tree.body))
    markers = tuple(t.marker for t in tokens if t.marker != 'import')
    assert markers == expected


def test_socket():
    text = """
        import socket
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        s.connect((HOST, PORT))
    """
    tree = astroid.parse(text)
    tokens = list(get_markers(body=tree.body))
    markers = tuple(t.marker for t in tokens)
    assert markers == ('import', 'network')


def test_asyncio_socket():
    text = """
        import asyncio
        r, w = await asyncio.open_connection('127.0.0.1', 8888)
    """
    tree = astroid.parse(text)
    print(tree.repr_tree())
    tokens = list(get_markers(body=tree.body))
    markers = tuple(t.marker for t in tokens)
    assert markers == ('import', 'network')


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

    ('__import__("something")', ('import', )),
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


def test_io_recursive_analize_body():
    text = """
    def inner(text):
        print(text)

    def outer():
        inner('hello')
    """
    text = dedent(text)
    tree = astroid.parse(text)
    print(tree.repr_tree())
    tokens = list(get_markers(body=tree.body[-1].body))
    markers = tuple(t.marker for t in tokens)
    assert markers == ('stdout', )


def test_io_recursive_explicit_markers():
    text = """
    @deal.has('io', invalid)
    @deal.raises()
    def inner(text):
        noting()

    def outer():
        inner('hello')
    """
    text = dedent(text)
    tree = astroid.parse(text)
    print(tree.repr_tree())
    tokens = list(get_markers(body=tree.body[-1].body))
    markers = tuple(t.marker for t in tokens)
    assert markers == ('io', )


def test_markers_from_stubs():
    text = """
    import ast

    nothing = None

    def do_nothing():
        pass

    @deal.has()
    def inner(text):
        ast.walk(None)
        not_resolvable()
        do_nothing()
        nothing()
    """
    text = dedent(text)
    tree = astroid.parse(text)
    print(tree.repr_tree())
    stubs = StubsManager()
    tokens = list(get_markers(body=tree.body[-1].body, stubs=stubs))
    markers = tuple(t.marker for t in tokens)
    assert markers == ('import', )
