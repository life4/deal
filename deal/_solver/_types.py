import typing
import astroid
import z3
from ._context import Context

Node = astroid.node_classes.NodeNG
Z3Nodes = typing.Iterable[z3.Z3PPObject]
HandlerType = typing.Callable[[Node, Context], Z3Nodes]
