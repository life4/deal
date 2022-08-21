from deal.linter._error import Error


def test_error():
    err = Error(row=1, col=2, code=3, text='check')
    assert tuple(err) == (1, 2, 'DEA003 check')
    assert str(err) == 'DEA003 check'
    assert repr(err).startswith('Error(')
