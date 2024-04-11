import mytyp

class Stack(mytyp.MyCollection):
    __parameters__ = [int]
    jtyp = "Stack"

    @classmethod
    def createNew(cls, vname, vkey, d):
        return mytyp.createNew_copy(cls, vname, "push", vkey, d)
    
lang = "Java"

def push(st: Stack, x: int) -> None: pass
push_def = (push, 'push', [0])

def pop(st: Stack) -> int: pass
pop_def = (pop, 'pop', [0])

def peek(st: Stack) -> int: pass
peek_def = (peek, 'peek', [])

def empty(st: Stack) -> bool: pass
empty_def = (empty, 'empty', [])

def search(st: Stack, x: int) -> int: pass
search_def = (search, 'search', [])

def size(st: Stack) -> int: pass
size_def = (size, 'size', [])

def isEmpty(st: Stack) -> bool: pass
isEmpty_def = (isEmpty, 'isEmpty', [])

#defs = [push_def, pop_def, peek_def, empty_def, size_def, isEmpty_def]
defs = [push_def, pop_def]
