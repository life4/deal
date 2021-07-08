import codecs

from pythonfuzz.main import PythonFuzz

import deal


def encode(text: str) -> str:
    return codecs.encode(text, encoding='rot13')


@deal.ensure(lambda text, result: encode(result) == text)
def decode(text: str) -> str:
    assert text != 'bad'
    return codecs.encode(text, encoding='rot13')


def fuzz():
    test = deal.cases(decode)
    PythonFuzz(test)()


if __name__ == '__main__':
    fuzz()
