import typing
from mytyp import MyTyp

#reverse, delete, insert, replace
class StringBuffer(MyTyp):
    fname = "StringBuffer"
    createNew = True  

class Char(MyTyp):
    createNew = False


lang = "Java"
typs_d = {typing.Any: "int", typing.List.__class__: "StringBuffer",
          str: "String"}

new_d = {"StringBuffer"}



def append_c(l: StringBuffer, s:str) -> None: pass
append_c_def = (append_c, 'append', [0])

# def append_s(l: typing.List[str], s:typing.List[str]) -> None: pass
# append_s_def = (append_s, 'append', [0])


# def reverse(l: typing.List[str]) -> None: pass
# reverse_def = (reverse, 'reverse', [0])

# def delete(l: typing.List[str], x:int, y:int) -> None: pass
# delete_def = (delete, 'delete', [0])

# def insert(offset: int, s:str) -> None: pass
# insert_def = (insert, 'insert', [0])


#defs = [append_c_def, reverse_def, delete_def, insert_def]
defs = [append_c_def]

