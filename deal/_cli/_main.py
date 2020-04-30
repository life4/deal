# built-in
from argparse import ArgumentParser
from types import MappingProxyType
from typing import Callable, Mapping, Sequence

# app
from ._lint import lint_command
from ._stub import stub_command


CommandsType = Mapping[str, Callable[[Sequence[str]], int]]
COMMANDS: CommandsType = MappingProxyType(dict(
    lint=lint_command,
    stub=stub_command,
))


def main(argv: Sequence[str], *, commands: CommandsType = COMMANDS) -> int:
    parser = ArgumentParser(prog='python3 -m deal')
    parser.add_argument('command', choices=sorted(commands))

    args, unknown_argv = parser.parse_known_args(argv)
    command = commands[args.command]
    return command(unknown_argv)
