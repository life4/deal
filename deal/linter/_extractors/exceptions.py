# built-in
import ast
import builtins
from typing import Iterator, Optional, Union

# external
import astroid

# app
from .common import TOKENS, Extractor, Token, get_name, infer
from .contracts import get_contracts


get_exceptions = Extractor()


@get_exceptions.register(*TOKENS.ASSERT)
def handle_assert(expr, **kwargs) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    return Token(value=AssertionError, **token_info)


# explicit raise
@get_exceptions.register(*TOKENS.RAISE)
def handle_raise(expr, **kwargs) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    name = get_name(expr.exc)
    if not name:
        # raised a value, too tricky
        if not isinstance(expr.exc, TOKENS.CALL):
            return None
        # raised an instance of an exception
        name = get_name(expr.exc.func)
        if not name or name[0].islower():
            return None
    exc = getattr(builtins, name, name)
    token_info['col'] = expr.exc.col_offset
    return Token(value=exc, **token_info)


# division by zero
@get_exceptions.register(*TOKENS.BIN_OP)
def handle_bin_op(expr, **kwargs) -> Optional[Token]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    if isinstance(expr.op, ast.Div) or expr.op == '/':
        if isinstance(expr.right, astroid.node_classes.NodeNG):
            guesses = infer(expr=expr.right)
            token_info['col'] = expr.right.col_offset
            for guess in guesses:
                if type(guess) is not astroid.Const:
                    continue
                return Token(value=ZeroDivisionError, **token_info)
        if isinstance(expr.right, ast.Num) and expr.right.n == 0:
            token_info['col'] = expr.right.col_offset
            return Token(value=ZeroDivisionError, **token_info)
    return None


# exit()
@get_exceptions.register(*TOKENS.CALL)
def handle_call(expr, dive: bool = True) -> Optional[Union[Token, Iterator[Token]]]:
    token_info = dict(line=expr.lineno, col=expr.col_offset)
    name = get_name(expr.func)
    if name and name == 'exit':
        return Token(value=SystemExit, **token_info)
    # sys.exit()
    if isinstance(expr.func, TOKENS.ATTR):
        name = get_name(expr.func)
        if name and name == 'sys.exit':
            return Token(value=SystemExit, **token_info)
    # infer function call and check the function body for raises
    if dive:
        return _exceptions_from_funcs(expr=expr)
    return None


@get_exceptions.register(astroid.Assign)
def handle_assign(expr: astroid.Assign, dive: bool = True) -> Iterator[Token]:
    # infer function call and check the function body for raises
    if dive:
        yield from _exceptions_from_funcs(expr=expr)


def _exceptions_from_funcs(expr) -> Iterator[Token]:
    for name_node in get_names(expr):
        # node have to be a name
        if type(name_node) is not astroid.Name:
            continue

        extra = dict(
            line=name_node.lineno,
            col=name_node.col_offset,
        )
        for value in infer(name_node):
            if type(value) is not astroid.FunctionDef:
                continue

            # recursively infer exceptions from the function body
            for error in get_exceptions(body=value.body, dive=False):
                yield Token(value=error.value, **extra)

            # get explicitly specified exceptions from `@deal.raises`
            if not value.decorators:
                continue
            for category, args in get_contracts(value.decorators.nodes):
                if category != 'raises':
                    continue
                for arg in args:
                    name = get_name(arg)
                    if name is None:
                        continue
                    yield Token(value=name, **extra)
    return None


def get_names(expr) -> Iterator:
    if isinstance(expr, astroid.Assign):
        yield from get_names(expr.value)
    if isinstance(expr, TOKENS.CALL):
        if isinstance(expr.func, TOKENS.NAME):
            yield expr.func
        for subnode in expr.args:
            yield from get_names(subnode)
        for subnode in (expr.keywords or ()):
            yield from get_names(subnode.value)
