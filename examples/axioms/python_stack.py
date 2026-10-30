"""Small mutable stack fixture for the axiom backend examples."""

import random


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


def integer_recipes(seed: int, count: int):
    generator = random.Random(seed)
    boundaries = [0, 1, -1, 2**31 - 1, -(2**31)]
    return [
        boundaries[index] if index < len(boundaries) else generator.randint(-10_000, 10_000)
        for index in range(count)
    ]


def hang(value: int) -> int:
    while True:
        value += 1


def impure_length(values: list[int]) -> int:
    values.append(99)
    return len(values)


_counter = 0


def nondeterministic(value: int) -> int:
    global _counter
    _counter += 1
    return value + _counter


def same_object(left, right) -> bool:
    return left is right


def noisy(value: int) -> int:
    print("x" * 10_000)
    return value


def crash(value: int) -> int:
    import os

    os._exit(value or 17)


class Utility:
    offset = 1

    @staticmethod
    def double(value: int) -> int:
        return value * 2

    @classmethod
    def plus_offset(cls, value: int) -> int:
        return value + cls.offset
