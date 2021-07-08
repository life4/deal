import sys
from argparse import ArgumentParser
from pathlib import Path
from types import MappingProxyType
from typing import Mapping, Sequence, TextIO, Type

from ._base import Command
from ._lint import LintCommand
from ._memtest import MemtestCommand
from ._prove import ProveCommand
from ._stub import StubCommand
from ._test import TestCommand


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
    parser.set_defaults(cmd=None)
    subparsers = parser.add_subparsers()
    for cmd_name, cmd_class in commands.items():
        descr = cmd_class.__doc__ or ''
        descr = (descr.splitlines() or [''])[0]
        subparser = subparsers.add_parser(
            name=cmd_name,
            description=descr,
        )
        cmd = cmd_class(stream=stream, root=root)
        cmd.init_parser(subparser)
        subparser.set_defaults(cmd=cmd)

    try:
        args = parser.parse_args(argv)
    except SystemExit as exc:
        return exc.code
    if args.cmd is None:
        main(['--help'], commands=commands, root=root, stream=stream)
        return 2
    return args.cmd(args)
