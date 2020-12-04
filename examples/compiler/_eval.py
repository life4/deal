
from dataclasses import dataclass
import deal


Value = int


class Node:
    def eval(self) -> Value:
        raise NotImplementedError


@dataclass
class IntNode(Node):
    value: Value

    def eval(self) -> Value:
        return self.value


@dataclass
class AddNode(Node):
    left: Node
    right: Node

    def eval(self) -> Value:
        return self.left.eval() + self.right.eval()


@deal.pure
def eval(node: Node) -> Value:
    return node.eval()
