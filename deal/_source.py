import inspect
import tokenize
from textwrap import dedent
from typing import Callable, List

from vaa._internal import Simple


TokensType = List[tokenize.TokenInfo]
processors = []


def processor(func: Callable[[TokensType], TokensType]) -> Callable[[TokensType], TokensType]:
    processors.append(func)
    return func


def get_validator_source(validator) -> str:
    # get source code
    if isinstance(validator, Simple):
        validator = validator.validator
    if not hasattr(validator, '__code__'):
        return ''
    try:
        lines, _ = inspect.getsourcelines(validator.__code__)
    except OSError:
        return ''
    lines = dedent('\n'.join(lines)).split('\n')

    # tokenize
    tokens: TokensType
    try:
        tokens = _get_tokens(lines)
    except tokenize.TokenError:
        lines = _clear_lines(lines)
        tokens = _get_tokens(lines)

    # drop junk
    for processor in processors:
        tokens = processor(tokens)

    # transform back to text
    lines = tokenize.untokenize(tokens).split('\n')
    lines = _clear_lines(lines)
    if len(lines) > 1:
        return ''
    return ' '.join(lines).replace('_.', '').lstrip()


def _clear_lines(lines: List[str]) -> List[str]:
    lines = [line.rstrip() for line in lines]
    lines = [line for line in lines if line]
    # drop trailing comma
    if lines[-1] and lines[-1][-1] == ',':
        lines[-1] = lines[-1][:-1]
    return lines


def _get_tokens(lines: List[str]) -> List[tokenize.TokenInfo]:
    tokens = tokenize.generate_tokens(iter(lines).__next__)
    exclude = {tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
    return [token for token in tokens if token.type not in exclude]


@processor
def _extract_def_name(tokens: TokensType) -> TokensType:
    for token, next_token in zip(tokens, tokens[1:]):
        if token.string == 'lambda':
            return tokens
        if token.string == '@':
            return tokens
        if token.string == 'def':
            return [next_token]
        if token.string == 'class':
            return [next_token]
    return tokens


@processor
def _drop_comments(tokens: TokensType) -> TokensType:
    return [token for token in tokens if token.type != tokenize.COMMENT]


@processor
def _extract_decorator_args(tokens: TokensType) -> TokensType:
    if not tokens:
        return tokens

    # drop decorator symbol
    if tokens[0].string == '@':
        tokens = tokens[1:]

    # proceed only if is call of a deal decorator
    if tokens[0].string != 'deal' or tokens[1].string != '.':
        return tokens

    # find where decorator starts
    start = 0
    for index, token in enumerate(tokens):
        if token.string == '(':
            start = index
            break
    else:
        return tokens
    start += 1

    end = 0
    for index, token in enumerate(tokens):
        if token.string == ')':
            end = index
    return tokens[start:end]


@processor
def _extract_assignment(tokens: TokensType) -> TokensType:
    start = 0
    for index, token in enumerate(tokens):
        if token.type == tokenize.OP and '=' in token.string:
            start = index
            break
        if token.type not in (tokenize.NAME, tokenize.DOT, tokenize.NEWLINE):
            return tokens
    else:
        return tokens
    start += 1
    return tokens[start:]


@processor
def _extract_lambda(tokens: TokensType) -> TokensType:
    start = 0
    for index, (token1, token2) in enumerate(zip(tokens, tokens[1:])):
        if token1.string != '(':
            continue
        if token2.string != 'lambda':
            continue
        start = index + 1
        break
    else:
        return tokens

    end = 0
    for index, token in enumerate(tokens[start:], start=start):
        if token.string == ')':
            end = index

    return tokens[start:end]


@processor
def _extract_lambda_body(tokens: TokensType) -> TokensType:
    # find where lambda starts
    start = 0
    for index, token in enumerate(tokens):
        if token.string == 'lambda':
            start = index + 1
            break
    else:
        return tokens

    # find where lambda body starts
    for index, token in enumerate(tokens[start:], start=start):
        if token.type == tokenize.OP and ':' in token.string:
            start = index
            break
    else:
        return tokens
    start += 1

    return tokens[start:]


@processor
def _fix_line_numbers(tokens: TokensType) -> TokensType:
    if not tokens:
        return tokens
    diff = tokens[0].start[0] - 1
    new_tokens = []
    for token in tokens:
        token = token._replace(
            start=(token.start[0] - diff, token.start[1]),
            end=(token.end[0] - diff, token.end[1]),
        )
        new_tokens.append(token)
    return new_tokens
