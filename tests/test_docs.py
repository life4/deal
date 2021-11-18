import re
from pathlib import Path
from textwrap import dedent

import pytest

import deal
from deal._cli._main import get_commands
from deal.linter._rules import CheckMarkers, rules


root = Path(__file__).parent.parent / 'docs'
rex_code = re.compile(r'```python\s+run\n(.+?)\n\s*```', re.DOTALL)


def get_code_blocks(path: Path):
    content = path.read_text()
    for match in rex_code.finditer(content):
        yield dedent(match.group(1))


def test_all_codes_listed():
    path = root / 'basic' / 'linter.md'
    content = path.read_text()
    for checker in rules:
        if type(checker) is CheckMarkers:
            continue
        line = '| DEAL{:03d} |'.format(checker.code)
        assert line in content

    for marker, code in CheckMarkers.codes.items():
        line = '| DEAL{:03d} | missed marker ({})'.format(code, marker)
        assert line in content


def test_all_marker_codes_listed():
    path = root / 'basic' / 'side-effects.md'
    content = path.read_text()
    lines = content.splitlines()
    for marker, code in CheckMarkers.codes.items():
        code_cell = '| DEAL{:03d} | '.format(code)
        assert code_cell in content
        for line in lines:
            if code_cell in line:
                assert marker in line
                break
        else:
            assert False, 'missing marker {}'.format(marker)


def test_cli_included():
    path = root / 'details' / 'cli.md'
    content = path.read_text()
    for name, cmd in get_commands().items():
        # has header
        tmpl = '## {n}\n\n'
        line = tmpl.format(n=name)
        assert line in content

        # has autodoc
        tmpl = '```{{eval-rst}}\n.. autofunction:: deal._cli._{n}.{c}\n```'
        line = tmpl.format(n=name, c=cmd.__name__)
        assert line in content

        # header and autodoc go next to each other
        tmpl = '## {n}\n\n```{{eval-rst}}\n.. autofunction:: deal._cli._{n}.{c}\n```'
        line = tmpl.format(n=name, c=cmd.__name__)
        assert line in content


def test_examples_included():
    path = root / 'details' / 'examples.md'
    content = path.read_text()
    for path in root.parent.joinpath('examples').iterdir():
        if '__' in path.name:
            continue
        # has header
        tmpl = '## {}\n\n'
        line = tmpl.format(path.stem)
        assert line in content

        # has include
        tmpl = '```{{eval-rst}}\n.. literalinclude:: ../../examples/{}\n```'
        line = tmpl.format(path.name)
        assert line in content


@pytest.mark.parametrize('name', deal.__all__)
def test_all_public_have_docstring(name: str):
    obj = getattr(deal, name)
    doc = obj.__doc__
    assert doc is not None, f'{name} has no docstring'


def test_all_public_listed_in_refs():
    path = root / 'basic' / 'refs.md'
    content = path.read_text()
    for name in deal.__all__:
        if name[0] == '_':
            continue
        if name in {'introspection', 'Scheme', 'TestCase'}:
            continue
        assert f'deal.{name}`' in content


def test_all_cli_commands_listed_in_refs():
    path = root / 'basic' / 'refs.md'
    content = path.read_text()
    for name, cmd in get_commands().items():
        assert f'`{name}`' in content
        assert f'`details/cli:{name}`' in content


def test_all_public_listed_in_api():
    path = root / 'details' / 'api.md'
    content = path.read_text()
    for name in deal.__all__:
        if name[0] == '_':
            continue
        if name in {'Scheme'}:
            continue
        assert f':: deal.{name}' in content


@pytest.mark.parametrize(
    'path',
    [pytest.param(p, id=p.name) for p in root.glob('**/*.md')],
)
def test_code_snippets(path: Path):
    for code in get_code_blocks(path):
        exec(code, dict(
            deal=deal,
            pytest=pytest,
        ))
