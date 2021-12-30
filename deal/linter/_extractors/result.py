import ast
from itertools import chain
from typing import List

import astroid

from .common import get_name, traverse


def uses_result(validator) -> bool:
    """Returns True if the validator uses `result` argument.

    It may directly list `result` as the argument,
    or it may be a simple validator and use `_.result` in the body.
    """
    if not isinstance(validator, (ast.Lambda, astroid.Lambda)):
        return True
    if _has_result_arg(validator):
        return True
    if _is_simple_validator(validator):
        return _simple_uses_result(validator)
    return False


def _has_result_arg(validator) -> bool:
    """Returns True if arguments list of the function has `result` argument.
    """
    if isinstance(validator, ast.Lambda):
        args = chain(
            validator.args.args,
            validator.args.kwonlyargs,
        )
        for arg in args:
            if arg.arg == 'result':
                return True
        return False
    if isinstance(validator, astroid.Lambda):
        assert isinstance(validator.args, astroid.Arguments)
        args = chain(
            validator.args.args,
            validator.args.kwonlyargs,
        )
        for arg in args:
            assert isinstance(arg, astroid.AssignName)
            if arg.name == 'result':
                return True
        return False
    raise RuntimeError('unreachable')


def _is_simple_validator(validator) -> bool:
    arg_names: List[str]
    if isinstance(validator, ast.Lambda):
        arg_names = [arg.arg for arg in validator.args.args]
    if isinstance(validator, astroid.Lambda):
        assert isinstance(validator.args, astroid.Arguments)
        arg_names = [arg.name for arg in validator.args.args]
    return arg_names == ['_']


def _simple_uses_result(validator) -> bool:
    """For simple validator, check if `_.result` is used in the body.
    """
    assert isinstance(validator, (ast.Lambda, astroid.Lambda))
    for node in traverse(body=[validator.body]):
        if get_name(node) == '_.result':
            return True
    return False
