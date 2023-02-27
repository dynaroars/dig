import random
import typing
import vu_common as CM

def convert_val(val):
    if isinstance(val, str):
        return '"{}"'.format(val)
    elif isinstance(val, bool):
        return str(val).lower()
    else:
        return str(val)
    
def get_jtyp(cls):
    try:
        typ = cls.jtyp
    except AttributeError:
        if cls is bool:
            typ = "boolean"
        elif cls is str:
            typ = "String"
        else:
            typ = cls.__name__
    return typ

def createNew_simple(cls, vname:str, vkey:str, d:dict):
    #int x = 5
    return "{} {} = {};".format(
        get_jtyp(cls), vname, convert_val(d[vkey]))

def createNew_new(cls, vname:str, vkey:str, d:dict):
    #String x = new String("hello")
    jtyp = get_jtyp(cls)
    return "{} {} = new {} ({});".format(
        jtyp, vname, jtyp, convert_val(d[vkey]) if vkey else '')

def createNew_copy(cls, vname:str, vadd:str, vkey:str, d:dict):
    elem = cls.__parameters__[0]
    ss = []
    col_name = "{}_col".format(vname)

    #int [] a = {1,2,3};
    s = "{} []{} = {{{}}};".format(
        get_jtyp(elem), col_name, ','.join(map(convert_val, d[vkey])))
    ss.append(s)
    # Stack v = new Stack();
    jtyp = get_jtyp(cls)
    s = "{} {} = new {}();".format(jtyp, vname, jtyp)
    ss.append(s)
    # for(int i = a.length-1; i>=0 ; --i) Stack.push(a.get(i))
    s = ("for(int i = {}.length-1; i>=0 ; --i) {}.{}({}[i]);"
         .format(col_name, vname, vadd, col_name))
    ss.append(s)
    ret = '\n'.join(ss)
    return ret

class MyTyp(object):
    @classmethod
    def is_valid_typ(cls, typ):
        return (typ is None or
                issubclass(typ, cls) or 
                typ.__name__ in set(
                    ["int", "bool", "str", "Any", "List"]))

    @classmethod
    def name(cls, t:str):
        """
        >>> assert Typ.name(typing.List[typing.Any]) == "Any_List"
        """
        
        if t is None:
            return str(None)
        
        tname = t.__name__
        assert '.' not in tname

        if tname == "List":
            params = t.__parameters__
            assert len(params) == 1
            subtyp = cls.name(params[0])
            tname = "{}_{}".format(subtyp, tname)

        return tname

    @classmethod
    def reprname(cls, t):
        """
        >>> assert Typ.reprname(int) == 'int'

        >>> t1 = typing.List[typing.Any]
        >>> assert Typ.reprname(t1) == 'typing.List[typing.Any]'
        """
        #basic types such as int, double, list
        if t.__class__.__name__ == 'type': 
            return t.__name__
        else:
            assert t is None or 'typing.' in repr(t), t
            return repr(t)    


def _createNew_simple(cls):
    return lambda vname, vkey, d: createNew_simple(cls, vname, vkey, d)

createNew_d = {int: _createNew_simple(int),
               bool: _createNew_simple(bool),
               str: _createNew_simple(str)}

class PyTyp(MyTyp):
    @classmethod
    def createNew(cls, vname, vkey, d):
        return createNew_simple(cls, vname, vkey, d)
    
class MyAny(PyTyp):
    ptyp = int
    jtyp = "int"
    @classmethod
    def createNew(cls, vname, vkey, d):
        return createNew_simple(cls, vname, vkey, d)
        

####    
class MyCollection(MyTyp):
    pass



class Example(object):
    container_siz = 5
    
    @classmethod
    def gen(cls, typ, is_empty):
        if issubclass(typ, MyCollection) or typ.__name__ == "List":
            n = random.randint(0, 0 if is_empty else cls.container_siz)
            params = typ.__parameters__
            assert len(params) == 1
            typ_ = params[0]
            ret = [cls.gen(typ_, is_empty) for _ in range(n)]
            
        elif issubclass(typ, PyTyp):
            return cls.gen(typ.ptyp, is_empty)
        
        elif typ.__name__ == "Any":
            ret = cls.gen(int, is_empty)
            
        elif typ.__name__ == "int":
            ret = random.randint(-50, 50)
            
        elif typ.__name__ == "bool":
            ret = random.choice([True, False])
            
        elif typ.__name__ == "str":
            ret = random.choice(
                ["", "zero", "one", "two", "three"])
        else:
            raise AssertionError("can't gen examples of typ '{}'".format(typ))
            
        return ret

def is_valid_def(d):
    return (isinstance(d, tuple) and len(d) == 3 and
            callable(d[0]) and
            isinstance(d[1], str) and d[1] and
            isinstance(d[2],list))
        
