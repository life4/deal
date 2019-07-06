import socket
import sys
from functools import partial, update_wrapper
from inspect import getcallargs
from io import StringIO
from types import MethodType
from typing import Callable, Type

from . import exceptions
from .schemes import is_scheme
from .state import state


class _Base:
    exception = exceptions.ContractError

    def __init__(self, validator, *, message: str = None,
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
        Step 4 (6 for invariant). Process contract (validator)
        """
        # Schemes validation interface
        if is_scheme(self.validator):
            params = getcallargs(self.function, *args, **kwargs)
            params.update(kwargs)
            validator = self.validator(data=params, request=None)
            if validator.is_valid():
                return
            raise self.exception(validator.errors)

        # Simple validation interface
        if hasattr(self.validator, 'is_valid'):
            validator = self.validator(*args, **kwargs)
            # is valid
            if validator.is_valid():
                return
            # is invalid
            if hasattr(validator, 'errors'):
                raise self.exception(validator.errors)
            if hasattr(validator, '_errors'):
                raise self.exception(validator._errors)
            raise self.exception

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


class Pre(_Base):
    """
    Check contract (validator) before function processing.
    Validate input arguments.
    """
    exception = exceptions.PreContractError

    def patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        self.validate(*args, **kwargs)
        return self.function(*args, **kwargs)


class Post(_Base):
    """
    Check contract (validator) after function processing.
    Validate output result.
    """
    exception = exceptions.PostContractError

    def patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        result = self.function(*args, **kwargs)
        self.validate(result)
        return result


class InvariantedClass:
    _disable_patching = False

    def _validate(self) -> None:
        """
        Step 5 (1st flow) or Step 4 (2nd flow). Process contract for object.
        """
        # disable methods matching before validation
        self._disable_patching = True
        # validation by Invariant.validate
        self._validate_base(self)
        # enable methods matching after validation
        self._disable_patching = False

    def _patched_method(self, method: Callable, *args, **kwargs):
        """
        Step 4 (1st flow). Call method
        """
        self._validate()
        result = method(*args, **kwargs)
        self._validate()
        return result

    def __getattribute__(self, name: str):
        """
        Step 3 (1st flow). Get method
        """
        attr = super().__getattribute__(name)
        # disable patching for InvariantedClass methods
        if name in ('_patched_method', '_validate', '_validate_base', '_disable_patching'):
            return attr
        # disable patching by flag (if validation in progress)
        if self._disable_patching:
            return attr
        # disable patching for attributes (not methods)
        if not isinstance(attr, MethodType):
            return attr
        # patch
        patched_method = partial(self._patched_method, attr)
        return update_wrapper(patched_method, attr)

    def __setattr__(self, name: str, value):
        """
        Step 3 (2nd flow). Set some attribute
        """
        # set
        super().__setattr__(name, value)
        if name == '_disable_patching':
            return
        # validation only after set
        self._validate()


class Invariant(_Base):
    exception = exceptions.InvContractError

    def validate_chain(self, *args, **kwargs) -> None:
        self.validate(*args, **kwargs)
        self.child_validator(*args, **kwargs)

    def __call__(self, _class: type):
        """
        Step 2. Return wrapped class.
        """
        # patch class parents and add method for validation

        # if already invarianted
        if hasattr(_class, '_validate_base'):
            self.child_validator = _class._validate_base
            patched_class = type(
                _class.__name__,
                (_class, ),
                {'_validate_base': self.validate_chain},
            )
        # if it's first invariant
        else:
            patched_class = type(
                _class.__name__ + 'Invarianted',
                (InvariantedClass, _class),
                {'_validate_base': self.validate},
            )
        # Magic: _validate_base method use Invariant as self, not _class

        # return update_wrapper(patched_class, _class)
        return patched_class


class Raises(_Base):
    exception = exceptions.RaisesContractError

    def __init__(self, *exceptions, message=None, exception=None, debug=False):
        """
        Step 1. Set allowed exceptions list.
        """
        self.exceptions = exceptions
        super().__init__(
            validator=None,
            message=message,
            exception=exception,
            debug=debug,
        )

    def patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        try:
            return self.function(*args, **kwargs)
        except exceptions.ContractError:
            raise
        except Exception as exc:
            if not isinstance(exc, self.exceptions):
                raise self.exception from exc
            raise


class Offline(_Base):
    exception = exceptions.OfflineContractError

    def __init__(self, *, message=None, exception=None, debug=False):
        """
        Step 1. Init params.
        """
        super().__init__(
            validator=None,
            message=message,
            exception=exception,
            debug=debug,
        )

    def patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        true_socket = socket.socket
        socket.socket = self.fake_socket
        try:
            return self.function(*args, **kwargs)
        finally:
            socket.socket = true_socket

    def fake_socket(self, *args, **kwargs):
        raise self.exception


class PatchedStringIO(StringIO):
    def __init__(self, exception):
        self.exception = exception

    def write(self, *args, **kwargs):
        raise self.exception


class Silent(Offline):
    exception = exceptions.SilentContractError

    def patched_function(self, *args, **kwargs):
        """
        Step 3. Wrapped function calling.
        """
        true_stdout = sys.stdout
        true_stderr = sys.stderr
        sys.stdout = PatchedStringIO(exception=self.exception)
        sys.stderr = PatchedStringIO(exception=self.exception)
        try:
            return self.function(*args, **kwargs)
        finally:
            sys.stdout = true_stdout
            sys.stderr = true_stderr
