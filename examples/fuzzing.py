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
    cases = deal.cases(decode)
    atheris.Setup(sys.argv, cases.fuzz)
    atheris.Fuzz()


if __name__ == '__main__':
    fuzz()
