import typing

lang = "Java"
typs_d = {typing.Any: "int", typing.List.__class__: "Stack"}


def lpush(l: typing.List[typing.Any], x:typing.Any) -> None: pass
lpush_def = (lpush, 'push', [0])

def lpop(l: typing.List[typing.Any]) -> typing.Any: pass
lpop_def = (lpop, 'pop', [0])

def lpeek(l: typing.List[typing.Any]) -> typing.Any: pass
lpeek_def = (lpeek, 'peek', [])

def lempty(l:typing.List[typing.Any]) -> bool: pass
lempty_def = (lempty, 'empty', [])

def lsearch(l: typing.List[typing.Any], x:typing.Any) -> int: pass
lsearch_def = (lsearch, 'search', [])

defs = [lpush_def, lpop_def, lpeek_def, lempty_def, lsearch_def]
#defs = [lpush_def, lpop_def, lempty_def]


