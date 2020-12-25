import typing

from ._context import Context
from ._exceptions import UnsupportedError
from ._types import Node, HandlerType, Z3Nodes


class HandlersRegistry:
    _handlers: typing.Dict[typing.Type[Node], HandlerType]

    def __init__(self) -> None:
        self._handlers = dict()

    def register(self, node: typing.Type[Node]) -> typing.Callable[[HandlerType], HandlerType]:
        assert node not in self._handlers

        def wrapper(handler: HandlerType) -> HandlerType:
            self._handlers[node] = handler
            return handler
        return wrapper

    def __call__(self, node: Node, ctx: Context) -> Z3Nodes:
        node_type = type(node)
        handler = self._handlers.get(node_type)
        if handler is None:
            raise UnsupportedError('unsupported ast node', node_type.__name__)
        return handler(node=node, ctx=ctx)
