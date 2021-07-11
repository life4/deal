from typing import Iterator
from ._decorators.base import Base


def get_contracts(func) -> Iterator[Base]:
    while True:
        cells = getattr(func, '__closure__', None)
        if cells:
            for cell in cells:
                obj = cell.cell_contents
                if isinstance(obj, Base):
                    yield obj
        if not hasattr(func, '__wrapped__'):
            return
        func = func.__wrapped__
