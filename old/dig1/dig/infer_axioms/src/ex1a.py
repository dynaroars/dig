import typing

lang = "Python"
typs_d = {typing.Any: "int", "List": "list"}

def linsert(l: typing.List[typing.Any], i:int, x:typing.Any) -> None: pass
linsert_def = (linsert, 'list.insert', [0])

def lextend(l1: typing.List[typing.Any], l2: typing.List[typing.Any]) -> None: pass
lextend_def = (lextend, 'list.extend', [0])

def lappend(l: typing.List[typing.Any], x:typing.Any) -> None: pass
lappend_def = (lappend, 'list.append', [0])

def lpop(l: typing.List[typing.Any]) -> typing.Any: pass
lpop_def = (lpop, 'list.pop', [0])

defs = [lpop_def, lappend_def, linsert_def, lextend_def]

