from argparse import ArgumentParser, Namespace
from pathlib import Path
from typing import TextIO


class Command:
    stream: TextIO
    root: Path

    def __init__(self, stream: TextIO, root: Path) -> None:
        self.stream = stream
        self.root = root

    def print(self, *args) -> None:
        print(*args, file=self.stream)

    @staticmethod
    def init_parser(parser: ArgumentParser) -> None:
        raise NotImplementedError

    def __call__(self, args: Namespace) -> int:
        raise NotImplementedError
