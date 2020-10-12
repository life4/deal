import inspect
import tokenize
from textwrap import dedent
from typing import List
from vaa._internal import Simple


def get_validator_source(validator) -> str:
    if isinstance(validator, Simple):
        validator = validator.validator
    if not hasattr(validator, '__code__'):
        return ''
    try:
        lines, _ = inspect.getsourcelines(validator.__code__)
    except OSError:
        return ''
    lines = dedent('\n'.join(lines)).split('\n')

    try:
        tokens = _get_tokens(lines)
    except tokenize.TokenError:
        lines = _clear_lines(lines)
        tokens = _get_tokens(lines)

    tokens = _drop_comments(tokens)
    tokens = _extract_decorator_args(tokens)
    tokens = _extract_assignment(tokens)
    tokens = _extract_lambda(tokens)
    tokens = _extract_lambda_body(tokens)
    tokens = _fix_line_numbers(tokens)
    tokens = _extract_function_name(tokens)

    lines = tokenize.untokenize(tokens).split('\n')
    lines = _clear_lines(lines)
    # drop trailing comma
    if lines[-1] and lines[-1][-1] == ',':
        lines[-1] = lines[-1][:-1]

    if len(lines) > 1:
        return ''
    return ' '.join(lines).replace('_.', '').lstrip()


def _clear_lines(lines: List[str]) -> List[str]:
    lines = [line.rstrip() for line in lines]
    lines = [line for line in lines if line]
    return lines


def _get_tokens(lines: List[str]) -> List[tokenize.TokenInfo]:
    tokens = tokenize.generate_tokens(iter(lines).__next__)
    # exclude = []
    exclude = {tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
    return [token for token in tokens if token.type not in exclude]


def _drop_comments(tokens: List[tokenize.TokenInfo]) -> List[tokenize.TokenInfo]:
    return [token for token in tokens if token.type != tokenize.COMMENT]


def _extract_decorator_args(tokens: List[tokenize.TokenInfo]) -> List[tokenize.TokenInfo]:

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


def _extract_assignment(tokens: List[tokenize.TokenInfo]) -> List[tokenize.TokenInfo]:
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


def _extract_lambda(tokens: List[tokenize.TokenInfo]) -> List[tokenize.TokenInfo]:
    start = 0
    for index, (token1, token2) in enumerate(zip(tokens, tokens[1:])):
        if tokens[0].string != '(':
            continue
        if tokens[1].string != 'lambda':
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


def _extract_lambda_body(tokens: List[tokenize.TokenInfo]) -> List[tokenize.TokenInfo]:
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


def _extract_function_name(tokens: List[tokenize.TokenInfo]) -> List[tokenize.TokenInfo]:
    for token, next_token in zip(tokens, tokens[1:]):
        if token.string == 'def':
            return [next_token]
    return tokens


def _fix_line_numbers(tokens: List[tokenize.TokenInfo]) -> List[tokenize.TokenInfo]:
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
