import typing
import astroid
from functools import partial

StmtType = typing.TypeVar('StmtType')


class IfTransformer:
    """
    If `if` statement has `return` anywhere inside the body,
    everything after the `if` statement must be considered as `else` branch.
    """

    def __init__(self):
        self._handlers = dict()

    def register(self):
        for node_class, handler in self._handlers.items():
            astroid.MANAGER.register_transform(
                node_class=node_class,
                transform=handler,
            )

    def unregister(self):
        for node_class, handler in self._handlers.items():
            astroid.MANAGER.unregister_transform(
                node_class=node_class,
                transform=handler,
            )

    def is_if_with_return(self, node):
        if not isinstance(node, astroid.If):
            return False
        if node.orelse:
            return False
        for subnode in node.body:
            if self._has_return(subnode):
                return True
        return False

    def _has_return(self, node):
        if isinstance(node, astroid.Return):
            return True
        if not isinstance(node, astroid.node_classes.Statement):
            return False
        for subnode in node.get_children():
            if self._has_return(subnode):
                return True
        return False

    def add_handler(self, node_class):
        def wrapper(handler_func):
            self._handlers[node_class] = partial(handler_func, self)
            return handler_func
        return wrapper

    def transform_body(self, nodes: typing.List[StmtType]) -> typing.List[StmtType]:
        for i, node in enumerate(nodes, start=1):
            if not self.is_if_with_return(node):
                continue
            assert isinstance(node, astroid.If)
            node.orelse = self.transform_body(nodes[i:])
            return nodes[:i]
        return nodes


if_transformer = IfTransformer()


@if_transformer.add_handler(astroid.ExceptHandler)
def handle_except(transformer: IfTransformer, node: astroid.ExceptHandler) -> astroid.ExceptHandler:
    node.body = transformer.transform_body(node.body)
    return node


@if_transformer.add_handler(astroid.For)
def handle_for(transformer: IfTransformer, node: astroid.For) -> astroid.ExceptHandler:
    node.body = transformer.transform_body(node.body)
    return node


@if_transformer.add_handler(astroid.If)
def handle_if(transformer: IfTransformer, node: astroid.If) -> astroid.ExceptHandler:
    node.body = transformer.transform_body(node.body)
    return node


@if_transformer.add_handler(astroid.TryExcept)
def handle_try(transformer: IfTransformer, node: astroid.TryExcept) -> astroid.ExceptHandler:
    node.body = transformer.transform_body(node.body)
    node.orelse = transformer.transform_body(node.orelse)
    return node


@if_transformer.add_handler(astroid.TryFinally)
def handle_try_finally(transformer: IfTransformer, node: astroid.TryFinally) -> astroid.ExceptHandler:
    node.body = transformer.transform_body(node.body)
    node.finalbody = transformer.transform_body(node.finalbody)
    return node


@if_transformer.add_handler(astroid.While)
def handle_while(transformer: IfTransformer, node: astroid.While) -> astroid.ExceptHandler:
    node.body = transformer.transform_body(node.body)
    node.orelse = transformer.transform_body(node.orelse)
    return node


@if_transformer.add_handler(astroid.With)
def handle_with(transformer: IfTransformer, node: astroid.With) -> astroid.ExceptHandler:
    node.body = transformer.transform_body(node.body)
    return node


@if_transformer.add_handler(astroid.FunctionDef)
def handle_func_def(transformer: IfTransformer, node: astroid.FunctionDef) -> astroid.ExceptHandler:
    node.body = transformer.transform_body(node.body)
    return node
