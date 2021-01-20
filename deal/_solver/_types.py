import typing

if typing.TYPE_CHECKING:
    from ._context import Context
    from ._proxies import ProxySort


class Z3Bool:
    def sort(self):
        pass

    def __getitem__(self, item):
        pass


Z3Node = Z3Bool
AstNode = typing.NewType('AstNode', object)      # astroid.node_classes.NodeNG
SortType = typing.Union[Z3Bool, 'ProxySort']
SortTypes = typing.Iterable[SortType]
HandlerType = typing.Callable[[AstNode, 'Context'], SortType]
