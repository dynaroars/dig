from beartype import beartype
import copy
from pathlib import Path
import pdb
DBG = pdb.set_trace
# This is not required if you've installed pycparser into
# your site-packages/ with setup.py

from pycparser import c_generator, c_ast, c_parser 
from helpers.vcommon import vwrite

class AddPrintfVisitor(c_ast.NodeVisitor):
    """
    add printf() calls to vtrace definitions
    """
    @beartype
    def __init__(self, vtrace:str) -> None:
        self.vtrace = vtrace

    @beartype
    def visit_FuncDef(self, node:c_ast.Node) -> None:
        if node.decl.name.startswith(self.vtrace) and not node.body.block_items:
            print(f"{node.decl.name} declared at {node.coord}")
            self._insert_funccall(node)

    @beartype
    def _insert_funccall(self,node:c_ast.FuncDef)-> None:
        myvars = [p.name for p in node.decl.type.args.params]
        printf_fcall  = self._create_printf(node.decl.name, myvars)
        node.body.block_items = [printf_fcall]



class AddPrintfInstr(AddPrintfVisitor):
    @beartype
    def _create_printf(self, myname:str, myvars:list[str]) -> c_ast.FuncCall:
        value = "; ".join("%d" for _ in myvars) + "\\n"
        myvars_ = [c_ast.ID(name=x)  for x in myvars]
        exprs = [c_ast.Constant(type="string", value=f'\"{myname}; {value}"')] + myvars_
        funcCall = c_ast.FuncCall(name=c_ast.ID(name="printf"),args=c_ast.ExprList(exprs=exprs))
        return funcCall    

class AddPrintfCivl(AddPrintfVisitor):
    @beartype
    def _create_printf(self, myname:str, myvars:list[str]) -> c_ast.FuncCall:
        value = "; ".join("%d" for _ in myvars) + "\\n"
        myvars_ = [c_ast.ID(name=x)  for x in myvars]
        exprs = [c_ast.Constant(type="string", value=f'\"{myname}; {value}"')] + myvars_
        funcCall = c_ast.FuncCall(name=c_ast.ID(name="printf"),args=c_ast.ExprList(exprs=exprs))
        return funcCall    
    
class ChangeVassertVisitor(c_ast.NodeVisitor):
    # change vassert call to assert or $assert calls

    @beartype
    def __init__(self, fname:str, changeto:str) -> None:
        self.fname = fname
        self.changeto = changeto
        
    @beartype
    def visit_FuncCall(self, node:c_ast.Node) -> None:
        if node.name.name == self.fname:
            print(f"{node.name.name} call at {node.coord}")
            self._change(node)

    @beartype
    def _change(self, fd:c_ast.FuncCall) -> None:
        fd.name.name = self.changeto


class PrintTypeVisitor(c_ast.NodeVisitor):
    # print vtrace1; I x; I y; I r; I q
    # also collect $input type name
    
    def __init__(self, vtrace:str, mainQ:str) -> None:
        self.vtrace = vtrace
        self.mainQ = mainQ
        self.inps = []
        
    def visit_FuncDef(self, node:c_ast.Node) -> None:
        
        if node.decl.name.startswith(self.vtrace) or node.decl.name == self.mainQ:
            nts = [(p.name , p.type.type.names[0]) for p in node.decl.type.args.params]
            nts = '; '.join(("I " if t == "int" else "D ") + n for n,t in nts)
            print(f"{node.decl.name}; {nts}")

        if node.decl.name == self.mainQ:
            inps = [(p.name , p.type.type.names[0]) for p in node.decl.type.args.params]
            self.inps = [f"$input {typ} {name};" for name, typ in inps]
             


    
# def show_func_calls(filename, vtrace):
#     ast = parse_file(filename, use_cpp=True)
#     v = FuncCallVisitor(vtrace)
#     v.visit(ast)


def _gen(myast, includes):
    generator = c_generator.CGenerator()
    instr = generator.visit(myast)
    instr = '\n'.join(includes + [instr])
    print(instr)
        
if __name__ == '__main__':

    filename = Path("../examples/transform/cohendiv.c")
    
    includes = []
    src = []
    for l in filename.read_text().split('\n'):
        l = l.strip()
        if l.startswith("#include"):
            includes.append(l)
        else:
            src.append(l)

    src = '\n'.join(src)
    #ast_instr.show()
    #DBG()
    parser = c_parser.CParser()
    
    
    #DBG()
    
    #trace instrumentation
    # ast_instr = parser.parse(src)
    # AddPrintfVisitor("vtrace").visit(ast_instr)
    # ChangeVassertVisitor("vassume", "assert").visit(ast_instr)
    # _gen(ast_instr, includes)

    
    
    #civl instrumentation
    ast_civl =  copy.deepcopy(parser.parse(src))
    
    ChangeVassertVisitor("vassume", "$assume").visit(ast_civl)
    AddPrintfCivl("vtrace").visit(ast_civl)
    vis = PrintTypeVisitor("vtrace", "mainQ")    
    vis.visit(ast_civl)
    includes = [i.replace('<','"').replace('>','"') for i in includes]
    inps = [inp for inp in vis.inps]
    _gen(ast_civl, ['#include "civlc.cvh"'] + includes + inps)
    
    
    
    
    
    
    #fn_new = filename + ".instr.c"
    # vwrite(fn_new, instr)
    #print(fn_new)
    
    # results = fc.results
    # if results:
    #     print(f"{len(results)} results")
    #     for r in results:
    #         insert_funccall(r)
            
    # print("Before:")
    # ast.show(offset=2)


    #create_funccall(myname="printf", myvars=["q","r","a","b"])
    
    # assign = ast.ext[0].body.block_items[0]
    # assign.lvalue.name = "y"
    # assign.rvalue.value = 2

    # print("After:")
    # ast.show(offset=2)
    # print("hello world")



    

    #compound = c_ast.Compound(block_items=[funcall, exprs])
    #compound.show()
# def translate_to_c(filename):
#     """ Simply use the c_generator module to emit a parsed AST.
#     """
#     ast = parse_file(filename, use_cpp=True,  cpp_path='gcc',
#                      cpp_args=['-E', r'-I../EXTERNAL_FILES/pyparser/utils/fake_libc_include'])
#     #generator = c_generator.CGenerator()
#     #print(generator.visit(ast))

#     ast.show(showcoord=True)

#     for ext in ast.ext:
#         print("helloworld")
#         if isinstance(ext, c_ast.FuncDef):
#             function_body = ext.body
#             print(type(ext.body))
#             # for decl in function_body.block_items:
#             #     decl.show()


# if __name__ == "__main__":
#     if len(sys.argv) > 1:
#         translate_to_c(sys.argv[1])
#     else:
#         print("Please provide a filename as argument")
