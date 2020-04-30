# external
import pytest

# project
from deal._cli import main


def test_calls_command():
    def cmd(argv):
        assert argv == ['a1', 'a2']
        return 13

    result = main(argv=['cmd', 'a1', 'a2'], commands=dict(cmd=cmd))
    assert result == 13


def test_unknown_command(capsys):
    with pytest.raises(SystemExit):
        main(argv=['unknown', 'a1', 'a2'], commands=dict(cmd=None))
    captured = capsys.readouterr()
    exp = "error: argument command: invalid choice: 'unknown' (choose from 'cmd')"
    assert exp in captured.err
