from ._tokenizer import IntToken, OpenToken, CloseToken, PlusToken, tokenize


def test_tokenize():
    assert tokenize('') == []
    assert tokenize('12') == [IntToken('12')]

    exp = [IntToken('12'), PlusToken(), IntToken('34')]
    assert tokenize('12 + 34') == exp

    exp = [
        OpenToken(), IntToken('12'), PlusToken(), IntToken('34'), CloseToken(),
        PlusToken(), IntToken('56'),
    ]
    assert tokenize('(12 + 34) + 56') == exp
