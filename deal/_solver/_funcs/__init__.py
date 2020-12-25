from ._registry import FUNCTIONS

# trigger registration of functions
from ._builtins import register as _    # noqa
from ._list import register as _        # noqa
from ._math import register as _        # noqa
from ._str import register as _         # noqa
from ._os_path import register as _     # noqa


__all__ = ['FUNCTIONS']
