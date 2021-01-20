# built-in
import typing

# app
from ._context import Context
from ._exceptions import UnsupportedError
from ._types import AstNode, HandlerType, SortType


class HandlersRegistry:
    _handlers: typing.Dict[typing.Type[AstNode], HandlerType]

    def __init__(self) -> None:
        self._handlers = dict()

    def register(self, node: typing.Type[AstNode]) -> typing.Callable[[HandlerType], HandlerType]:
        assert node not in self._handlers

        def wrapper(handler: HandlerType) -> HandlerType:
            self._handlers[node] = handler
            return handler
        return wrapper

    def __call__(self, node: AstNode, ctx: Context) -> SortType:
        node_type = type(node)
        handler = self._handlers.get(node_type)
        if handler is None:
            raise UnsupportedError('unsupported ast node', node_type.__name__)
        return handler(node, ctx)
