# built-in
import inspect
from asyncio import iscoroutinefunction
from contextlib import suppress
from functools import update_wrapper
from typing import Callable, Type

import vaa

# app
from .._exceptions import ContractError
from .._state import state
from .._types import ExceptionType


class Base:
    exception: ExceptionType = ContractError

    def __init__(self, validator: Callable, *, message: str = None,
                 exception: Type[ExceptionType] = None, debug: bool = False):
        """
        Step 1. Set contract (validator).
        """
        self.validator = self._make_validator(validator, message=message)
        self.debug = debug
        if exception:
            self.exception = exception
        if message:
            self.exception = self.exception(message)    # type: ignore

    @staticmethod
    def _make_validator(validator, message: str):
        # implicitly wrap in vaa all external validators
        with suppress(TypeError):
            return vaa.wrap(validator, simple=False)

        # implicitly wrap in vaa.simple only funcs with one `_` argument.
        if inspect.isfunction(validator):
            params = inspect.signature(validator).parameters
            if set(params) == {'_'}:
                return vaa.simple(validator, error=message)

        return validator

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

        # if it is a decorator for a function, convert positional args into named ones.
        if hasattr(self, 'function'):
            # detect original function
            function = self.function
            while hasattr(function, '__wrapped__'):
                function = function.__wrapped__     # type: ignore
            # assign *args to real names
            params.update(inspect.getcallargs(function, *args, **kwargs))
            # drop args-kwargs, we already put them on the right places
            for bad_name in ('args', 'kwargs'):
                if bad_name in params and bad_name not in kwargs:
                    del params[bad_name]

        # validate
        validator = self.validator(data=params)
        if validator.is_valid():
            return

        # if no errors returned, raise the default exception
        errors = validator.errors
        if not errors:
            raise self.exception

        # Flatten single error without field to one simple str message.
        # This is for better readability of simple validators.
        if type(errors) is list:
            if type(errors[0]) is vaa.Error:
                if len(errors) == 1:
                    if errors[0].field is None:
                        errors = errors[0].message

        # raise errors
        if isinstance(self.exception, Exception):
            raise type(self.exception)(errors)
        raise self.exception(errors)

    def _simple_validation(self, *args, **kwargs) -> None:
        validation_result = self.validator(*args, **kwargs)
        # is invalid (validator returns error message)
        if isinstance(validation_result, str):
            if isinstance(self.exception, Exception):
                raise type(self.exception)(validation_result)
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

        async def async_wrapped(*args, **kwargs):
            if self.enabled:
                return await self.async_patched_function(*args, **kwargs)
            else:
                return await function(*args, **kwargs)

        def wrapped_generator(*args, **kwargs):
            if self.enabled:
                yield from self.patched_generator(*args, **kwargs)
            else:
                yield from function(*args, **kwargs)

        if iscoroutinefunction(function):
            return update_wrapper(async_wrapped, function)
        if inspect.isgeneratorfunction(function):
            return update_wrapper(wrapped_generator, function)
        return update_wrapper(wrapped, function)
