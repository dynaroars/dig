import abc
import typing
import sys
import os.path
import itertools
import typing
from collections import Counter

import vu_common as CM
import config as CC
import mytyp

logger = CM.VLog(os.path.basename(__file__))
logger.level = CC.logger_level
CM.VLog.PRINT_TIME = False

class Lang(object):
    __metaclass__ = abc.ABCMeta

    @classmethod
    def mk_fun_t(cls, tid, code:list, comment, out_p:tuple, test_d) -> (str, str):
        code = '\n    '.join(c(test_d) if callable(c) else c for c in code)
        ret_val, ret_typ = out_p
        assert ret_typ is bool, ret_typ
        
        fname = "t_{}".format(tid)
        fbody = cls.test_body(fname, code, ret_val, comment)        
        fname = fname + "()"
        return fname, fbody

    @classmethod 
    def mk_fun_g(cls, mid, code:list, comment:str, out_p:tuple,
                 ntests:int, vars_d:dict) -> (str, str):
        assert isinstance(code, list) and code, code
        assert isinstance(out_p, tuple) and len(out_p) == 2, out_p
        assert isinstance(ntests, int)and ntests > 0, ntests

        def gen_example(i):
            ret = {v: mytyp.Example.gen(t, i==0) for v,t in vars_d}
            return ret
        
        funs = [cls.mk_fun_t("{}_{}".format(mid, i),
                             code, comment, out_p, gen_example(i))
                  for i in range(ntests)]

        return cls.mk_fun(mid, funs, cls.connector_and, cls.gexceptions)

    @classmethod
    def mk_fun_f(cls, mid, codes, comment:str,
                 term_val:bool, ntests:int, vars_d:dict) -> (str, str):
        assert isinstance(mid, str)
        assert isinstance(codes, list) and codes
        assert isinstance(comment, str)        
        assert isinstance(term_val, bool)
        
        def _outp(outp):
            if cls.is_soft_check(term_val, outp):
                return cls.true_val, bool
            else:
                return outp
        
        funs = [cls.mk_fun_g("{}_{}".format(mid, i), code, comment, 
                               _outp(out_p), ntests, vars_d)
                  for i, (code, _, out_p) in enumerate(codes)]

        return cls.mk_fun(mid, funs, cls.connector_or, None)

    @classmethod
    def mk_fun(cls, mid, funs, connector:str, exceptions:list):
        fun_calls, fun_codes = zip(*funs)
        assert len(fun_calls)

        if len(fun_calls) == 1:
            return fun_calls[0], fun_codes[0]
        else:
            call = connector.join(fun_calls)
            code = '\n'.join(fun_codes)

            fname = "f_{}".format(mid)
            ecall = cls.ecall_body(call, exceptions)
            fbody = cls.fun_template(fname, ecall, code, "boolean")

            fname = fname + "()"
            return fname, fbody

    @classmethod
    def get_stat(cls, stat:str):
        stat_l = stat.lower()
        if stat_l == "true":
            ret = True
        elif stat_l == "false":
            ret = False
        else:
            raise AssertionError("Unknown result: {}".format(stat))
        return ret
    
    @classmethod
    def myrun(cls, code):
        filename = "Test"
        filename_ext = filename + cls.file_ext
        CM.vwrite(filename_ext, code)
        
        if cls.cmd_compile:
            cmd = cls.cmd_compile.format(filename_ext)
            logger.debug("cmd {}".format(cmd))
            logger.detail(cmd)
            rs, rs_err = CM.vcmd(cmd)

            assert not rs_err, rs_err.decode('ascii')
            assert not rs, rs.decode('ascii')
        
        cmd = cls.cmd_run.format(filename)
        logger.debug("cmd: {}".format(cmd))
        rs, rs_err = CM.vcmd(cmd)
        assert not rs_err, rs_err.decode('ascii')
        rs = rs.decode('ascii').strip()
        stats = [cls.get_stat(stat.strip()) for stat in rs.split()]
        return stats        
    
    @classmethod
    def mk_var(cls, vname:str, used:Counter) -> str:
        new_vname = vname + str(used[vname])
        used[vname] += 1        
        return new_vname

    @classmethod
    def is_soft_check(cls, is_axiomeq:bool, out_p:(None, tuple)):
        """
        soft_check = True
        hard_check => False
        """
        if out_p is None:
            return True
        else:
            ret_val, ret_typ = out_p
            if is_axiomeq:
                return False
            else:
                return True
    
class Python(Lang):
    connector_and = " and "
    connector_or = " or "
    true_val = "True"
    false_val = "False"
    gexceptions = [("IndexError", false_val)]
    cmd_compile = None
    cmd_run = "python {}.py"
    file_ext = ".py"

    @classmethod
    def test_body(cls, fname, fbody, ret_val, comment=""):
        code = """
# {}
def {}():
    {}
    return {}""".format(comment, fname, fbody, ret_val)
        return code

    @classmethod
    def ecall_body(cls, call, exceptions:list):
        if not exceptions:
            return "return ({})".format(call)
        else:
            eblock = """
    except {}:
        return {}"""
            
            eb ='\n'.join(eblock.format(e,r) for e,r in exceptions)

            ecall = \
 """try:
        return ({})
    {}""".format(call, eb)

            return ecall

    @classmethod
    def fun_template(cls, fname:str, ecall:str, rest:str, ret_typ:str):
        code = \
"""{}
def {}():
    {}
        """.format(rest, fname, ecall)
        return code
        
    @classmethod
    def mk_fun_main(cls, fnames_fbodies:typing.List[tuple]):
        fnames,fbodies = zip(*fnames_fbodies)
        rest = '\n'.join(fbodies)
        call = ', '.join("{}".format(fname) for fname in fnames)
        call = "[{}]".format(call)
                           
        code = \
"""{}
results = {}
print('\\n'.join(map(str, results)))""".format(rest, call)
        return code

    
    @classmethod
    def gen_code_arg(cls, vname, vtyp, vkey:str, typs_d:dict):
        return lambda d: "{} = {}".format(vname, d[vkey])
    
    @classmethod
    def gen_code_fun_f3(cls, term_val:str, term_call:str, term_typ,
                        vs:typing.List[str],
                        used_vars:Counter, typs_d:dict):
        
        #compute code and out
        if term_val == "eq":
            assert len(vs) == 2
            code = "{} {} {}".format(vs[0], term_call, vs[1])
        else:
            assert vs
            code = "{}({})".format(term_call, ', '.join(vs))
            
        if term_typ:
            varname = "{}_ret".format(term_val.replace(".","_"))
            varname = cls.mk_var(varname, used_vars)
            out = (varname, term_typ)
            code = "{} = {}".format(varname, code)            
        else:
            out = None

        return code, out
    
class Java(Lang):
    connector_and = " && "
    connector_or = " || "
    true_val = "true"
    false_val = "false"
    gexceptions = [("EmptyStackException", false_val),
                   ("java.util.NoSuchElementException", false_val),
                   ("java.lang.IndexOutOfBoundsException", false_val)
    ]
    cmd_compile = "javac {}"
    cmd_run = "java {}"
    file_ext = ".java"

    @classmethod
    def test_body(cls, fname, code, ret_val, comment=""):
        body = """
        //{}
        @SuppressWarnings("unchecked")
        private static boolean {}(){{
        {}
            return {};
        }}
        """.format(comment, fname, code, ret_val)
        return body

    @classmethod
    def ecall_body(cls, call, exceptions:list):
        if not exceptions:
            ecall = "return ({});".format(call)
        else:
            eblock = """
            catch({} e){{return {};}}"""
            eblock =''.join(eblock.format(e,r) for e,r in exceptions)
            ecall = """
            try{{return ({});}}{}
            """.format(call, eblock)
        return ecall

    @classmethod
    def fun_template(cls, fname:str, ecall:str, code:str, ret_typ:str):
        fbody =  """
        private static {} {}(){{
            {}
        }}
        
        {}
        """.format(ret_typ, fname, ecall, code)
        return fbody

    @classmethod
    def mk_fun_main(cls, fnames_fbodies):
        fnames,fbodies = zip(*fnames_fbodies)
        fnames = '\n'.join("System.out.println({});"
                           .format(fname) for fname in fnames)
        fbodies = '\n'.join(fbodies)
        
        code = """
import java.util.*;
public class Test{{
    public static void main(String args[]){{
        {}
     }}
     {}
    }}""".format(fnames, fbodies)
        return code

    @classmethod
    def gen_code_arg(cls, vname, vtyp, vkey:str, typs_d:dict):
        assert issubclass(vtyp, mytyp.MyTyp) or vtyp in mytyp.createNew_d, vtyp
        try:
            fun = vtyp.createNew
        except AttributeError:
            fun = mytyp.createNew_d[vtyp]
        return lambda d: fun(vname, vkey, d)


    @classmethod
    def gen_code_fun_f3(cls, term_val:str, term_call:str, term_typ,
                        vs:typing.List[str],
                        used_vars:Counter, typs_d:dict):
        
        #compute code and out
        if term_val == "eq":
            assert len(vs) == 2
            #vs0 == vs1;
            code = "{} {} {}".format(vs[0], term_call, vs[1])
        else:
            assert vs
            #vs0.call(vs1,vs2,..)
            code = "{}.{}({})".format(vs[0], term_call, ','.join(vs[1:]))
            
        if term_typ:
            varname = "{}_ret".format(term_val.replace(".","_"))
            varname = cls.mk_var(varname, used_vars)
            out = (varname, term_typ)
            jtyp = mytyp.get_jtyp(term_typ)
            code = "{} {} = ({})({})".format(jtyp, varname, jtyp, code)
        else:
            out = None
        code = code + ";"
        
        return code, out
        
if __name__ == "__main__":
    import doctest
    doctest.testmod()
          
