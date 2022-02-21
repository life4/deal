from asyncio import iscoroutinefunction
from functools import update_wrapper
from inspect import isgeneratorfunction
from typing import (
    TYPE_CHECKING, Callable, Dict, Generic, List, Optional, Tuple, Type, TypeVar,
)

from .._exceptions import ContractError
from .._state import state


if TYPE_CHECKING:
    from ._has_patcher import HasPatcher
    from ._validators import RaisesValidator, ReasonValidator, Validator


F = TypeVar('F', bound=Callable)
ATTR = '__deal_contract'


class Contracts(Generic[F]):
    __slots__ = (
        'func',
        'wrapped',
        'pres',
        'posts',
        'ensures',
        'examples',
        'raises',
        'reasons',
        'patcher',
    )

    func: F
    wrapped: F
    pres: List['Validator']
    posts: List['Validator']
    ensures: List['Validator']
    examples: List['Validator']
    raises: List['RaisesValidator']
    reasons: List['ReasonValidator']
    patcher: Optional['HasPatcher']

    def __init__(self, func: F) -> None:
        self.func = func
        self.pres = []
        self.posts = []
        self.ensures = []
        self.examples = []
        self.raises = []
        self.reasons = []
        self.patcher = None

    @classmethod
    def attach(cls, contract_type: str, validator: 'Validator', func: F) -> F:
        contracts = cls._ensure_wrapped(func)
        validator.function = func
        getattr(contracts, contract_type).append(validator)
        return contracts.wrapped

    @classmethod
    def attach_has(cls, patcher: 'HasPatcher', func: F) -> F:
        contracts = cls._ensure_wrapped(func)
        contracts.patcher = patcher
        return contracts.wrapped

    @classmethod
    def _ensure_wrapped(cls: Type['Contracts'], func: F) -> 'Contracts[F]':
        contracts: Contracts
        contracts = getattr(func, ATTR, None)  # type: ignore[assignment]
        if contracts is not None:
            return contracts
        contracts = cls(func)
        assert contracts is not None

        if iscoroutinefunction(func):
            async def wrapper(*args, **kwargs):
                return await contracts._run_async(args, kwargs)
        elif isgeneratorfunction(func):
            def wrapper(*args, **kwargs):
                yield from contracts._run_iter(args, kwargs)
        else:
            def wrapper(*args, **kwargs):
                return contracts._run_sync(args, kwargs)

        update_wrapper(wrapper=wrapper, wrapped=func)
        setattr(wrapper, ATTR, contracts)
        contracts.wrapped = wrapper
        return contracts

    def wrap(self, func: F) -> F:
        """Wrap the function with the contracts.
        """
        contracts = self._ensure_wrapped(func)
        contracts.pres.extend(self.pres)
        contracts.posts.extend(self.posts)
        contracts.ensures.extend(self.ensures)
        contracts.examples.extend(self.examples)
        contracts.raises.extend(self.raises)
        contracts.reasons.extend(self.reasons)
        if self.patcher is not None:
            if contracts.patcher is not None:
                contracts.patcher.markers |= self.patcher.markers
            else:
                contracts.patcher = self.patcher
        return contracts.wrapped

    def _run_sync(self, args: Tuple[object, ...], kwargs: Dict[str, object]):
        if not state.debug:
            return self.func(*args, **kwargs)

        # pre-validation
        state.debug = False
        try:
            for validator in self.pres:
                validator.validate(args, kwargs)
        finally:
            state.debug = True

        # running the function
        if self.patcher is not None:
            self.patcher.patch()
        try:
            result = self.func(*args, **kwargs)
        except ContractError:
            raise
        except Exception as exc:
            for validator in self.raises:
                validator.validate(args, kwargs, exc=exc)
            exc_type = type(exc)
            for validator in self.reasons:
                if exc_type is validator.event:
                    validator.validate(args, kwargs, exc=exc)
            raise
        finally:
            if self.patcher is not None:
                self.patcher.unpatch()

        # post-validation
        state.debug = False
        try:
            for validator in self.posts:
                validator.validate((result,), {})
            for validator in self.ensures:
                validator.validate(args, dict(kwargs, result=result))
        finally:
            state.debug = True

        return result

    async def _run_async(self, args: Tuple[object, ...], kwargs: Dict[str, object]):
        if not state.debug:
            return await self.func(*args, **kwargs)

        # pre-validation
        state.debug = False
        try:
            for validator in self.pres:
                validator.validate(args, kwargs)
        finally:
            state.debug = True

        # running the function
        if self.patcher is not None:
            self.patcher.patch()
        try:
            result = await self.func(*args, **kwargs)
        except ContractError:
            raise
        except Exception as exc:
            for validator in self.raises:
                validator.validate(args, kwargs, exc=exc)
            exc_type = type(exc)
            for validator in self.reasons:
                if exc_type is validator.event:
                    validator.validate(args, kwargs, exc=exc)
            raise
        finally:
            if self.patcher is not None:
                self.patcher.unpatch()

        # post-validation
        state.debug = False
        try:
            for validator in self.posts:
                validator.validate((result,), {})
            for validator in self.ensures:
                validator.validate(args, dict(kwargs, result=result))
        finally:
            state.debug = True

        return result

    def _run_iter(self, args: Tuple[object, ...], kwargs: Dict[str, object]):
        if not state.debug:
            yield from self.func(*args, **kwargs)
            return

        # pre-validation
        state.debug = False
        try:
            for validator in self.pres:
                validator.validate(args, kwargs)
        finally:
            state.debug = True

        generator = self.func(*args, **kwargs)
        while True:
            # running the function
            if self.patcher is not None:
                self.patcher.patch()
            try:
                result = next(generator)
            except StopIteration:
                return
            except ContractError:
                raise
            except Exception as exc:
                for validator in self.raises:
                    validator.validate(args, kwargs, exc=exc)
                exc_type = type(exc)
                for validator in self.reasons:
                    if exc_type is validator.event:
                        validator.validate(args, kwargs, exc=exc)
                raise
            finally:
                if self.patcher is not None:
                    self.patcher.unpatch()

            # post-validation
            state.debug = False
            try:
                for validator in self.posts:
                    validator.validate((result,), {})
                for validator in self.ensures:
                    validator.validate(args, dict(kwargs, result=result))
            finally:
                state.debug = True
            yield result
