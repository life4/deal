import re
from dataclasses import dataclass
from typing import ClassVar, List, Optional, Type

import deal


tokenizers: List[Type['Token']] = []


def register_tokenizer(tokenizer: Type['Token']) -> Type['Token']:
    tokenizers.append(tokenizer)
    return tokenizer


class Token:
    value: ClassVar[str]

    @classmethod
    @deal.pure
    def match(cls, content: str) -> Optional['Token']:
        if not content:
            return None
        if content[0] == cls.value:
            return cls()
        return None

    @property
    def width(self):
        return 1


@register_tokenizer
@dataclass
class OpenToken(Token):
    value = '('


@register_tokenizer
@dataclass
class CloseToken(Token):
    value = ')'


@register_tokenizer
@dataclass
class PlusToken(Token):
    value = '+'


@register_tokenizer
@dataclass
class IntToken(Token):
    value: str
    _rex = re.compile(r'\d+')

    @classmethod
    @deal.pure
    def match(cls, content: str) -> Optional['Token']:
        if not content:
            return None
        match = cls._rex.match(content)
        if match:
            return cls(match.group(0))
        return None

    @property
    def width(self):
        return len(self.value)


class ParseError(Exception):
    def __str__(self) -> str:
        msg = super().__str__()
        return repr(msg)


@deal.raises(ParseError)
def tokenize(content: str) -> List[Token]:
    tokens = []
    content = content.lstrip()
    while content:
        for tokenizer in tokenizers:
            token = tokenizer.match(content)
            if not token:
                continue
            tokens.append(token)
            content = content[token.width:]
            break
        else:
            raise ParseError(content)
        content = content.lstrip()
    return tokens
