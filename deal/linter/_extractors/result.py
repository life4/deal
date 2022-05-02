from __future__ import annotations

import ast
from itertools import chain
from typing import TYPE_CHECKING

from .common import get_name, traverse, TOKENS

if TYPE_CHECKING:
    import astroid


def uses_result(validator) -> bool:
    """Returns True if the validator uses `result` argument.

    It may directly list `result` as the argument,
    or it may be a simple validator and use `_.result` in the body.
    """
    if not isinstance(validator, TOKENS.LAMBDA):
        return True
    if _has_result_arg(validator):
        return True
    if _is_simple_validator(validator):
        return _simple_uses_result(validator)
    return False


def _has_result_arg(validator: ast.Lambda | astroid.Lambda) -> bool:
    """Returns True if arguments list of the function has `result` argument.
    """
    if isinstance(validator, ast.Lambda):
        args = chain(
            validator.args.args,
            validator.args.kwonlyargs,
        )
        arg1: ast.arg
        for arg1 in args:
            if arg1.arg == 'result':
                return True
        return False
    else:
        args = chain(
            validator.args.args,
            validator.args.kwonlyargs,
        )
        arg2: astroid.AssignName
        for arg2 in args:
            if arg2.name == 'result':
                return True
        return False


def _is_simple_validator(validator: ast.Lambda | astroid.Lambda) -> bool:
    arg_names: list[str]
    if isinstance(validator, ast.Lambda):
        arg_names = [arg.arg for arg in validator.args.args]
    else:
        arg_names = [arg.name for arg in validator.args.args]
    return arg_names == ['_']


def _simple_uses_result(validator: ast.Lambda | astroid.Lambda) -> bool:
    """For simple validator, check if `_.result` is used in the body.
    """
    for node in traverse(body=[validator.body]):
        if get_name(node) == '_.result':
            return True
    return False
