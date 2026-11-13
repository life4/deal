from typing import Any, Callable, Type, Union


ExceptionType = Union[Exception, Type[Exception]]


# A validator is a function, a short validator, or a `vaa`-compatible schema.
ValidatorType = Callable[..., Any]
