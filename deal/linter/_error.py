# built-in
import typing


ERROR_FORMAT = 'DEAL{code:03d}: {text}'


class Error:
    def __init__(self, *, row: int, col: int, code: int, text: str, value: str = None):
        self.row = row
        self.col = col
        self.code = code
        self.text = text
        self.value = value

    @property
    def message(self) -> str:
        msg = ERROR_FORMAT.format(code=self.code, text=self.text)
        if self.value:
            msg += ' ({})'.format(self.value)
        return msg

    def __iter__(self) -> typing.Iterator[typing.Union[int, str]]:
        yield self.row
        yield self.col
        yield self.message

    def __str__(self) -> str:
        return self.message

    def __repr__(self) -> str:
        return '{name}({content!r})'.format(
            name=type(self).__name__,
            content=self.__dict__,
        )

    def __hash__(self):
        return hash((self.row, self.col, self.code))
