# built-in
from inspect import getfile

# project
import deal


@deal.raises()
def f():
    a
    1 / 0
    return getfile(deal)
