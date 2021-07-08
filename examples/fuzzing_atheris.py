"""
Get help for libFuzzer:
    python3 examples/fuzzing_atheris.py -help=1

Run 1000 test cases:
    python3 examples/fuzzing_atheris.py -runs=1000
"""
import codecs
import sys

import atheris

import deal


def encode(text: str) -> str:
    return codecs.encode(text, encoding='rot13')


@deal.ensure(lambda text, result: encode(result) == text)
def decode(text: str) -> str:
    assert text != 'bad'
    return codecs.encode(text, encoding='rot13')


def fuzz():
    test = deal.cases(decode)
    atheris.Setup(sys.argv, test)
    atheris.Fuzz()


if __name__ == '__main__':
    fuzz()
