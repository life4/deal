from argparse import ArgumentParser

from deal._cli import main
from deal._cli._base import Command


class FakeCommand(Command):
    @staticmethod
    def init_parser(parser: ArgumentParser) -> None:
        parser.add_argument('args', nargs='*')

    def __call__(self, args) -> int:
        assert args.args == ['a1', 'a2']
        return 13


def test_calls_command():
    result = main(argv=['fake', 'a1', 'a2'], commands=dict(fake=FakeCommand))
    assert result == 13


def test_unknown_command(capsys):
    result = main(argv=['unknown', 'a1', 'a2'], commands=dict(fake=FakeCommand))
    assert result == 2
    captured = capsys.readouterr()
    exp = "invalid choice: 'unknown' (choose from 'fake')"
    assert exp in captured.err


def test_no_command_specified(capsys):
    result = main(argv=[], commands=dict(fake=FakeCommand))
    assert result == 2
    captured = capsys.readouterr()
    assert 'positional arguments:' in captured.out
    assert 'fake' in captured.out
