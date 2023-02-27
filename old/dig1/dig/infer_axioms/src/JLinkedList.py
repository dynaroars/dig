import mytyp

class JLinkedList(mytyp.MyCollection):
    __parameters__ = [int]
    jtyp = "LinkedList"

    @classmethod
    def createNew(cls, vname, vkey, d):
        return mytyp.createNew_copy(cls, vname, "add", vkey, d)

    
lang = "Java"

def add(ll: JLinkedList, e: int) -> None: pass
add_def = (add, 'add', [0])

def addLast(ll: JLinkedList, e: int) -> None: pass
addLast_def = (addLast, 'addLast', [0])

def addFirst(ll: JLinkedList, e: int) -> None: pass
addFirst_def = (addFirst, 'addFirst', [0])

def remove(ll: JLinkedList, e: int) -> int: pass
remove_def = (remove, 'remove', [0])

def removeLast(ll: JLinkedList) -> int: pass
removeLast_def = (removeLast, 'removeLast', [0])

def removeFirst(ll: JLinkedList) -> int: pass
removeFirst_def = (removeFirst, 'removeFirst', [0])

def clear(ll: JLinkedList) -> None: pass
clear_def = (clear, 'clear', [0])


def clone(ll: JLinkedList) -> JLinkedList: pass
clone_def = (clone, 'clone', [])

def contains(ll:JLinkedList, e:int) -> bool: pass
contains_def = (contains, 'contains', [])

def element(ll:JLinkedList) -> int: pass
element_def = (element, 'element', [])


def get(ll:JLinkedList, index:int) -> int: pass
get_def = (get, 'get', [])


def getFirst(ll:JLinkedList) -> int: pass
getFirst_def = (getFirst, 'getFirst', [])


def getLast(ll:JLinkedList) -> int: pass
getLast_def = (getLast, 'getLast', [])


defs = [add_def, addFirst_def, addLast_def,
        remove_def, removeFirst_def, removeLast_def,
        clear_def, clone_def, contains_def, element_def,
        get_def, getFirst_def, getLast_def]


# defs = [add_def, addFirst_def, addLast_def,
#         remove_def, removeFirst_def, removeLast_def,
#         clear_def]
