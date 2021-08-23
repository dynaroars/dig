import typing

lang = "Java"

def fake(s:str) -> str: pass
fake_def = (fake, 'fake', [])
def concat(s:str, x:str) -> str:pass
concat_def = (concat, 'concat', [])

def isEmpty(s:str) -> bool: pass
isEmpty_def = (isEmpty, 'isEmpty', [])


def slength(s:str) -> int: pass
slength_def = (slength, 'length', [])

defs = [fake_def, isEmpty_def]


