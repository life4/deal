import typing


ERROR_FORMAT = 'DEAL{code:03d}'


class Error:
    __slots__ = ('row', 'col', 'code', 'text', 'value')

    def __init__(
        self, *,
        row: int,
        col: int,
        code: int,
        text: str,
        value: typing.Optional[str] = None,
    ) -> None:
        self.row = row
        self.col = col
        self.code = code
        self.text = text
        self.value = value

    @property
    def full_code(self) -> str:
        return ERROR_FORMAT.format(code=self.code)

    @property
    def message(self) -> str:
        msg = self.full_code + ' ' + self.text
        if self.value:
            msg += f' ({self.value})'
        return msg

    def __iter__(self) -> typing.Iterator[typing.Union[int, str]]:
        yield self.row
        yield self.col
        yield self.message

    def __str__(self) -> str:
        return self.message

    def __repr__(self) -> str:
        name = type(self).__name__
        return f'{name}(row={self.row}, col={self.col}, code={self.code})'

    def __hash__(self) -> int:
        return hash((self.row, self.col, self.code))
