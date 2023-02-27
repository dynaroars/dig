    @classmethod    
    def run(cls, codes:typing.List[str],
            term_val:str, out_p:(None, tuple)) -> bool:
        if cls.is_soft_check(term_val, out_p):
            out_p = "true", bool
        
        code = cls.mk_code(codes, out_p)
        classname = "Test"
        filename = classname + ".java"
        CM.vwrite(filename, code)

        cmd = "javac {}".format(filename)
        rs, rs_err = CM.vcmd(cmd)
        assert not rs_err, rs_err.decode('ascii')
        assert not rs, rs.decode('ascii')
        
        cmd = "java {}".format(classname)
        rs, rs_err = CM.vcmd(cmd)
        if rs_err:
            rs_err = rs_err.decode('ascii')
            raise AssertionError(rs_err)
        else:
            rs = rs.decode('ascii').strip()
            if rs == "true":
                ret = True
            elif rs == "false":
                ret = False
            elif "EmptyStackException" in rs:
                ret = False
            else:
                raise AssertionError("Unknown result: {}".format(rs))
        return ret

    @classmethod
    def mk_main(cls, call:str, code:str):
        s = """
import java.util.*;
public class Test{{
    @SuppressWarnings("unchecked")
    public static void main(String args[]){{
        {}
     }}
     {}
    }}""".format(call, code)
        return s
        
    @classmethod
    def mk_code(cls, codes:typing.List[str], out_p:tuple) -> str:
        
        call, code = cls.mk_fun_test(0, codes, out_p)
        return cls.mk_main(call, code)

    @classmethod
    def mk_fun_test(cls, i:int, codes:typing.List[str], out_p:tuple) -> str:
        test_funs = [cls.mk_fun_itest(i, code, out_p)
                     for i, code in enumerate(codes)]
        
        names, tests = zip(*test_funs)

        #test0() && test1() ...
        call = ' && '.join("{}()".format(name) for name in names)        
        #boolean test1(...){}  ; boolean test2(..){} ;
        tests = '\n'.join(tests)

        fun_name = "ftest_{}".format(i)
        code =  """
        @SuppressWarnings("unchecked")
        private static void {}(){{
            try{{
                System.out.println({});
            }}
            catch(EmptyStackException e){{
                System.out.println("Error: EmptyStackException");
            }}
   
        }}
        
        {}
        """.format(fun_name, call, tests)
        call = "{}();".format(fun_name)
        return call ,code

    @classmethod
    def mk_fun_itest(cls, i:int, code:str, out_p:tuple):
        ret_val, ret_typ = out_p
        name = "test{}".format(i)
        fun = """
        @SuppressWarnings("unchecked")
        private static boolean {}(){{
            {}
            return {};
        }}
        """.format(name, code, ret_val)
        return name, fun


        



        
        # fun_t_calls, fun_t_codes = zip(*funs)
        # call = " && ".join(fun_t_calls)
        # code = '\n'.join(fun_t_codes)
        
        # fname = "g_{}".format(mid)

        # fbody =  """
        # @SuppressWarnings("unchecked")
        # private static boolean {}(){{
        #     try{{
        #         return ({});
        #     }}
        #     catch(EmptyStackException e){{
        #         return false;
        #     }}
        # }}
        
        # {}
        # """.format(fname, call, code)
        # fname = fname + "()"
        # return fname, fbody    
    

            @classmethod
    def get_typs(cls, typ, typs_d):
        """
        >>> typs_d = {typing.Any: "int", "List": "Stack", str: "String", typing.List.__class__: "Stack1"}
        >>> assert Java.get_typs(str, typs_d) == (None, 'String')
        >>> assert Java.get_typs(int, typs_d) == (None, 'int')
        >>> assert Java.get_typs(typing.Any, typs_d) == (None, 'int')
        >>> assert Java.get_typs(typing.List[typing.Any], typs_d) == ('Stack', 'int')
        >>> assert Java.get_typs(typing.List[int], typs_d) == ('Stack', 'int')
        >>> assert Java.get_typs(typing.List, typs_d) == ('Stack', None)
        >>> assert Java.get_typs(bool, typs_d) == (None, 'boolean')
        """
        col_typ_str = None
        elem_typ_str = None

        prims_d = {bool: "boolean"}
        if typ.__class__.__name__ == "type":  #primitive Python types
            if typ in typs_d:
                elem_typ_str = typs_d[typ]
            elif typ in cls.l_typs_d:
                elem_typ_str = cls.l_typs_d[typ]
            else:
                elem_typ_str = typ.__name__
            
        elif typ is typing.Any:
            elem_typ_str = typs_d[typ]
        elif type(typ) is typing.TypeVar:#  ~T
            elem_typ_str = None
        elif typ.__name__ == "List":
                col_typ_str = typs_d[typ.__name__]
                params = typ.__parameters__
                assert len(params) == 1
                col_typ_str_, elem_typ_str = cls.get_typs(params[0], typs_d)
                assert col_typ_str_ is None
        else:
            raise AssertionError("unrecognized typ {}".format(typ))

        return col_typ_str, elem_typ_str
