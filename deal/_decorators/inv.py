from functools import partial, update_wrapper
from types import MethodType
from typing import Callable

from .._exceptions import InvContractError
from .._types import ExceptionType
from .base import Base, CallableType


class InvariantedClass:
    _disable_patching: bool = False

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


class Invariant(Base[CallableType]):
    exception: ExceptionType = InvContractError

    def validate(self, obj) -> None:  # type: ignore
        """
        Step 6. Process contract (validator)
        """

        if hasattr(self.validator, 'is_valid') and hasattr(obj, '__dict__'):
            kwargs = obj.__dict__.copy()
            kwargs.pop('_disable_patching', '')
            self._vaa_validation(**kwargs)
        else:
            self._simple_validation(obj)

    def validate_chain(self, *args, **kwargs) -> None:
        self.validate(*args, **kwargs)
        self.child_validator(*args, **kwargs)

    def __call__(self, _class: type):  # type: ignore
        """
        Step 2. Return wrapped class.
        """
        # patch class parents and add method for validation

        # if already invarianted
        if hasattr(_class, '_validate_base'):
            self.child_validator = _class._validate_base  # type: ignore
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
