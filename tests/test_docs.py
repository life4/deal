from pathlib import Path
from deal.linter._rules import rules, CheckMarkers
from deal._cli._main import COMMANDS


root = Path(__file__).parent.parent / 'docs'


def test_all_codes_listed():
    path = root / 'basic' / 'linter.md'
    content = path.read_text()
    for checker in rules:
        if type(checker) is CheckMarkers:
            continue
        code = '| DEAL{:03d} |'.format(checker.code)
        assert code in content

    for marker, code in CheckMarkers.codes.items():
        code = '| DEAL{:03d} | missed marker ({})'.format(code, marker)
        assert code in content


def test_cli_included():
    path = root / 'details' / 'cli.md'
    content = path.read_text()
    for name, cmd in COMMANDS.items():
        # has header
        tmpl = '## {n}\n\n'
        line = tmpl.format(n=name)
        assert line in content

        # has autodoc
        tmpl = '```eval_rst\n.. autofunction:: deal._cli._{n}.{c}\n```'
        line = tmpl.format(n=name, c=cmd.__name__)
        assert line in content

        # header and autodoc go next to each other
        tmpl = '## {n}\n\n```eval_rst\n.. autofunction:: deal._cli._{n}.{c}\n```'
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
        tmpl = '```eval_rst\n.. literalinclude:: ../../examples/{}\n```'
        line = tmpl.format(path.name)
        assert line in content
