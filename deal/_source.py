import inspect
import tokenize
from textwrap import dedent
from typing import List


def get_validator_source(validator) -> str:
    if not hasattr(validator, '__code__'):
        return ''
    try:
        lines, _ = inspect.getsourcelines(validator.__code__)
    except OSError:
        return ''
    if not lines:
        return ''
    lines = dedent('\n'.join(lines)).split('\n')

    # extract contract from decorator arguments
    lines = _drop_comments(lines)
    lines = _extract_decorator_args(lines)
    lines = _extract_assignment(lines)
    lines = _extract_lambda_body(lines)

    # drop trailing spaces and empty lines
    lines = '\n'.join(lines).rstrip().split('\n')
    # drop trailing comma
    if lines[-1] and lines[-1][-1] == ',':
        lines[-1] = lines[-1][:-1]

    if len(lines) > 1:
        return ''
    return ' '.join(lines)


def _cut_lines(lines: List[str], first_token, last_token):
    lines = lines.copy()
    # drop unrelated lines
    first_line = first_token.start[0] - 1
    last_line = last_token.end[0]
    lines = lines[first_line:last_line]

    # drop unrelated symbols
    first_col = first_token.start[-1]
    last_col = last_token.end[-1]
    lines[-1] = lines[-1][:last_col]
    lines[0] = lines[0][first_col:]

    return lines


def _get_tokens(lines: List[str]):
    return list(tokenize.generate_tokens(iter(lines).__next__))


def _drop_comments(lines: List[str]):
    tokens = _get_tokens(lines)
    for token in tokens:
        if token.type != tokenize.COMMENT:
            continue
        row, col = token.start
        lines[row - 1] = lines[row - 1][:col].rstrip()
    return lines


def _extract_decorator_args(lines: List[str]):
    tokens = _get_tokens(lines)

    # drop decorator symbol
    if tokens[0].string == '@':
        tokens = tokens[1:]

    # proceed only if is call of a deal decorator
    if tokens[0].string != 'deal':
        return lines
    if tokens[1].string != '.':
        return lines

    # find where decorator starts
    start = 0
    for index, token in enumerate(tokens):
        if token.string == '(':
            start = index
            break
    else:
        start = 0
    first_token = tokens[start + 1]

    end = 0
    for index, token in enumerate(tokens):
        if token.string == ')':
            end = index
    last_token = tokens[end - 1]
    return _cut_lines(lines, first_token, last_token)


def _extract_assignment(lines: List[str]):
    tokens = _get_tokens(lines)

    if tokens[0].type != tokenize.NAME:
        return lines

    # find where body starts
    start = 0
    for index, token in enumerate(tokens):
        if token.type == tokenize.OP and '=' in token.string:
            start = index
            break
        if token.type not in (tokenize.NAME, tokenize.DOT):
            return lines
    else:
        return lines
    first_token = tokens[start + 1]
    last_token = tokens[-2]
    return _cut_lines(lines, first_token, last_token)


def _extract_lambda_body(lines: List[str]):
    tokens = _get_tokens(lines)

    if tokens[0].string != 'lambda':
        return lines

    # find where body starts
    start = 0
    for index, token in enumerate(tokens):
        if token.type == tokenize.OP and ':' in token.string:
            start = index
            break
    else:
        return lines
    first_token = tokens[start + 1]
    last_token = tokens[-2]
    return _cut_lines(lines, first_token, last_token)
