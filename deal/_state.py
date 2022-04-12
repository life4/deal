from __future__ import annotations

import os
import warnings
from types import MappingProxyType
from typing import Callable, Mapping, TypeVar


T = TypeVar('T', bound=Callable)
PERMAMENT_ERROR = RuntimeError('contracts are permanently disabled')
PROD_ENV = MappingProxyType(dict(
    LAMBDA_TASK_ROOT='AWS',
    GCLOUD_PROJECT='GCP',
))
TEST_ENV = MappingProxyType(dict(
    PYTEST_CURRENT_TEST='pytest',
    CI='CI',
))


class _State:
    __slots__ = ('debug', 'removed', 'color')
    debug: bool
    removed: bool
    color: bool

    def __init__(self) -> None:
        self.removed = False
        self.reset()

    def reset(self) -> None:
        """Restore contracts state to the default.

        All contracts are disabled on production by default.
        See [runtime][runtime] documentation.

        [runtime]: https://deal.readthedocs.io/basic/runtime.html
        """
        if self.removed:
            raise PERMAMENT_ERROR
        self.debug = __debug__
        self.color = 'NO_COLOR' not in os.environ

    def enable(self, warn: bool = True) -> None:
        """Enable all contracts.

        By default, deal will do a few sanity checks to make sure you haven't
        unintentionally enabled contracts on a production environment.
        Pass `warn=False` to disable this behavior.
        """
        if self.removed:
            raise PERMAMENT_ERROR
        self.debug = True
        if warn:
            # coverage freaks out here on Python 3.10
            if not __debug__:  # pragma: no cover
                msg = 'It is production but deal is enabled. Is it intentional?'
                warnings.warn(msg, category=RuntimeWarning)
            else:
                self._warn_if(PROD_ENV, 'enabled')

    def disable(self, *, permament: bool = False, warn: bool = True) -> None:
        """Disable all contracts.

        If `permament=True`, contracts are permanently disabled
        for the current interpreter runtime and cannot be turned on again.

        By default, deal will do a few sanity checks to make sure you haven't
        unintentionally disabled contracts on a test environment.
        Pass `warn=False` to disable this behavior.
        """
        if self.removed and permament:
            raise PERMAMENT_ERROR
        self.debug = False
        self.removed = permament
        if warn:
            self._warn_if(TEST_ENV, 'disabled')

    def _warn_if(self, env_vars: Mapping[str, str], state: str) -> None:
        for var, env in env_vars.items():
            if not os.environ.get(var):
                continue
            msg = f'It is {env} but deal is {state}. Is it intentional?'
            warnings.warn(msg, category=RuntimeWarning)
            return


state = _State()
reset = state.reset
enable = state.enable
disable = state.disable
