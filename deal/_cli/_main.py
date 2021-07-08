import sys
from argparse import ArgumentParser
from pathlib import Path
from types import MappingProxyType
from typing import TextIO, Type, Mapping, Sequence

from ._lint import LintCommand
from ._memtest import MemtestCommand
from ._prove import ProveCommand
from ._stub import StubCommand
from ._test import TestCommand
from ._base import Command


CommandsType = Mapping[str, Type[Command]]
COMMANDS: CommandsType = MappingProxyType(dict(
    lint=LintCommand,
    memtest=MemtestCommand,
    prove=ProveCommand,
    stub=StubCommand,
    test=TestCommand,
))


def main(
    argv: Sequence[str], *,
    commands: CommandsType = COMMANDS,
    root: Path = None,
    stream: TextIO = sys.stdout,
) -> int:
    if root is None:  # pragma: no cover
        root = Path()
    parser = ArgumentParser(prog='python3 -m deal')
    subparsers = parser.add_subparsers()
    for cmd_name, cmd_class in commands.items():
        subparser = subparsers.add_parser(cmd_name)
        cmd = cmd_class(stream=stream, root=root)
        cmd.init_parser(subparser)
        subparser.set_defaults(cmd=cmd)

    args = parser.parse_args(argv)
    return args.cmd(args)
