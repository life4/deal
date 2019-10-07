# built-in
from functools import update_wrapper
from inspect import getcallargs
from typing import Callable, Type

# app
from .._exceptions import ContractError
from .._state import state
from .._types import ExceptionType


class Base:
    exception: ExceptionType = ContractError

    def __init__(self, validator: Callable, *, message: str = None,
                 exception: Type[Exception] = None, debug: bool = False):
        """
        Step 1. Set contract (validator).
        """
        self.validator = validator
        self.debug = debug
        if exception:
            self.exception = exception
        if message:
            self.exception = self.exception(message)

    def validate(self, *args, **kwargs) -> None:
        """
        Step 4. Process contract (validator)
        """

        if hasattr(self.validator, 'is_valid'):
            self._vaa_validation(*args, **kwargs)
        else:
            self._simple_validation(*args, **kwargs)

    def _vaa_validation(self, *args, **kwargs) -> None:
        params = kwargs.copy()
        if hasattr(self, 'function'):
            # detect original function
            function = self.function
            while hasattr(function, '__wrapped__'):
                function = function.__wrapped__
            # assign *args to real names
            params.update(getcallargs(function, *args, **kwargs))
            # drop args-kwargs, we already put them on the right places
            for bad_name in ('args', 'kwargs'):
                if bad_name in params and bad_name not in kwargs:
                    del params[bad_name]

        validator = self.validator(data=params)
        if validator.is_valid():
            return
        raise self.exception(validator.errors)

    def _simple_validation(self, *args, **kwargs) -> None:
        validation_result = self.validator(*args, **kwargs)
        # is invalid (validator return error message)
        if isinstance(validation_result, str):
            raise self.exception(validation_result)
        # is valid (truely result)
        if validation_result:
            return
        # is invalid (falsy result)
        raise self.exception

    @property
    def enabled(self) -> bool:
        if self.debug:
            return state.debug
        else:
            return state.main

    def __call__(self, function: Callable) -> Callable:
        """
        Step 2. Return wrapped function.
        """
        self.function = function

        def wrapped(*args, **kwargs):
            if self.enabled:
                return self.patched_function(*args, **kwargs)
            else:
                return function(*args, **kwargs)

        return update_wrapper(wrapped, function)
