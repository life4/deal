from inspect import getfile

import deal


@deal.raises()
def f():
    a
    1 / 0
    return getfile(deal)
