"""
Graham Hutton's Razor

Implementation and property testing of it:
    https://www.youtube.com/watch?v=T_IINWzQhow
References:
    https://stackoverflow.com/q/17870864/8704691
Graham Hutton:
    http://www.cs.nott.ac.uk/~pszgmh/
"""

from dataclasses import dataclass
from typing import Generic, Optional, TypeVar
import deal


Value = int
T = TypeVar('T')


# -- Tree-based solution (evaluation) -- #


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


def test_eval():
    assert eval(IntNode(4)) == 4

    node = AddNode(IntNode(2), IntNode(3))
    assert eval(node) == 2 + 3

    node = AddNode(IntNode(3), IntNode(4))
    node = AddNode(IntNode(2), node)
    assert eval(node) == 2 + 3 + 4


# -- Stack-based solution (execution) -- #


class EmptyStack(Exception):
    pass


@dataclass
class Stack(Generic[T]):
    head: Optional[T]
    tail: Optional['Stack']

    @classmethod
    def make_empty(cls):
        return cls(head=None, tail=None)

    def push(self, value: T) -> 'Stack':
        return Stack(head=value, tail=self)


@dataclass
class Op:
    def exec(self, stack: Stack[Value]) -> Stack[Value]:
        raise NotImplementedError


@dataclass
class PushOp(Op):
    value: Value

    def exec(self, stack: Stack[Value]) -> Stack[Value]:
        return stack.push(self.value)


@dataclass
class AddOp(Op):
    def exec(self, stack: Stack[Value]) -> Stack[Value]:
        left = stack.head
        if left is None:
            raise EmptyStack
        stack = stack.tail

        right = stack.head
        if right is None:
            raise EmptyStack
        stack = stack.tail

        return stack.push(left + right)


def exec(operations: Stack[Op]) -> Optional[Value]:
    values = Stack.make_empty()
    while operations.head:
        values = operations.head.exec(values)
        if not operations.tail:
            return
        operations = operations.tail
    return values.head


def test_exec():
    ops = Stack.make_empty()
    ops = ops.push(PushOp(10))
    assert exec(ops) == 10

    ops = Stack.make_empty()
    ops = ops.push(AddOp())
    ops = ops.push(PushOp(3))
    ops = ops.push(PushOp(4))
    assert exec(ops) == 3 + 4
