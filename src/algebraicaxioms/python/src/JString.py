import mytyp

class MyStr(mytyp.PyTyp):
    ptyp = str
    jtyp = "String"

    @classmethod
    def createNew(cls, vname, vkey, d):
        return cls.createNew_new(vname, vkey, d)


lang = "Java"

def concat(s:str, x:str) -> str:pass
concat_def = (concat, 'concat', [])

def isEmpty(s:str) -> bool: pass
isEmpty_def = (isEmpty, 'isEmpty', [])


def slength(s:str) -> int: pass
slength_def = (slength, 'length', [])

defs = [isEmpty_def, slength_def]


