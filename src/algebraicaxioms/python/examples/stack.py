import mytyp

class Stack(mytyp.MyCollection):
    __parameters__ = [int]
    jtyp = "Stack"

    @classmethod
    def createNew(cls, vname, vkey, d):
        return mytyp.createNew_copy(cls, vname, vkey, d)

    
lang = "Java"
typs_d = {}

def push(st: Stack, x: mytyp.MyAny) -> None: pass
push_def = (push, 'push', [0])

def pop(st: Stack) -> mytyp.MyAny: pass
pop_def = (pop, 'pop', [0])

def peek(st: Stack) -> mytyp.MyAny: pass
peek_def = (peek, 'peek', [])

def empty(st: Stack) -> bool: pass
empty_def = (empty, 'empty', [])

def search(st: Stack, x: mytyp.MyAny) -> int: pass
search_def = (search, 'search', [])


defs = [push_def, pop_def, peek_def, empty_def,  search_def]
