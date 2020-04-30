# built-in
from argparse import ArgumentParser
from typing import Sequence

# app
from ._lint import lint_command
from ._stub import stub_command


def get_parser() -> ArgumentParser:
    parser = ArgumentParser(prog='python3 -m deal')
    parser.add_argument('command', choices=['lint', 'stub'])
    return parser


COMMANDS = dict(lint=lint_command, stub=stub_command)


def main(argv: Sequence[str]) -> int:
    parser = get_parser()
    args, unknown = parser.parse_known_args(argv)
    command = COMMANDS[args.command]
    return command(unknown)
