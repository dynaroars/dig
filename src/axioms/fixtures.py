"""Administrator-installed, deterministic fixtures allowed by hosted axiom mode."""


class Stack:
    def __init__(self, values=()):
        self.values = list(values)

    def push(self, item: int) -> int:
        self.values.append(item)
        return item

    def pop(self) -> int:
        return self.values.pop()

    def peek(self) -> int:
        return self.values[-1]


def stack_from_recipe(value):
    return Stack(value)


def stack_snapshot(stack: Stack):
    return list(stack.values)
