
from dataclasses import dataclass
from typing import Generic, Optional, TypeVar
import deal


Value = int
T = TypeVar('T')


class EmptyStack(Exception):
    pass


@dataclass
class Stack(Generic[T]):
    head: Optional[T]
    tail: Optional['Stack']

    @classmethod
    def make_empty(cls):
        return cls(head=None, tail=None)

    @classmethod
    def from_list(cls, values: T) -> 'Stack[T]':
        stack = cls.make_empty()
        for value in values:
            stack = stack.push(value)
        return stack

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


@deal.raises(EmptyStack)
def exec(operations: Stack[Op]) -> Optional[Value]:
    values = Stack.make_empty()
    while operations.head:
        values = operations.head.exec(values)
        if not operations.tail:
            return
        operations = operations.tail
    return values.head
