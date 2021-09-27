from types import MappingProxyType
from typing import Callable, Iterator

from .. import _decorators
from . import _wrappers
from ._wrappers import Contract


WRAPPERS = MappingProxyType({
    _decorators.Ensure: _wrappers.Ensure,
    _decorators.Example: _wrappers.Example,
    _decorators.Has: _wrappers.Has,
    _decorators.Post: _wrappers.Post,
    _decorators.Pre: _wrappers.Pre,
    _decorators.Raises: _wrappers.Raises,
    _decorators.Reason: _wrappers.Reason,
})


def get_contracts(func: Callable) -> Iterator[Contract]:
    while True:
        cells = getattr(func, '__closure__', None)
        if cells:
            for cell in cells:
                obj = cell.cell_contents
                wrapper = WRAPPERS.get(type(obj))
                if wrapper is None:
                    continue
                yield wrapper(obj)
        if not hasattr(func, '__wrapped__'):
            return
        func = func.__wrapped__  # type: ignore[attr-defined]
