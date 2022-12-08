from __future__ import print_function
from beartype import beartype
import sys
import pdb
DBG = pdb.set_trace
# This is not required if you've installed pycparser into
# your site-packages/ with setup.py

from pycparser import parse_file, c_generator, c_ast, c_parser 

text = r"""
void vtrace1(int q, int r, int a, int b){

}
"""
# void func(void)
# {
#   x = 1;
# }

# void vtrace1(int q, int r, int a, int b){
# printf("%d %d %d\n",q,r, a, b);
#



class AddPrintfVisitor(c_ast.NodeVisitor):

    @beartype
    def __init__(self, funcname:str) -> None:
        self.funcname = funcname

    @beartype
    def visit_FuncDef(self, node:c_ast.Node) -> None:
        if node.decl.name.startswith(self.funcname) and not node.body.block_items:
            print('%s declared at %s' % (self.funcname, node.coord))
            self.insert_funccall(node)


    @beartype
    def insert_funccall(self,node:c_ast.FuncDef)->None:
        myvars = [p.name for p in node.decl.type.args.params]
        printf_fcall  = self.create_printf(node.decl.name, myvars)
        node.body.block_items = [printf_fcall]

    @beartype
    def create_printf(self, myname:str, myvars:list[str]) -> c_ast.FuncCall:
        value = "; ".join("%d" for _ in myvars) + "\\n"
        myvars_ = [c_ast.ID(name=x)  for x in myvars]
        exprs = [c_ast.Constant(type="string", value=f'\"{myname}; {value}"')] + myvars_
        funcCall = c_ast.FuncCall(name=c_ast.ID(name="printf"),args=c_ast.ExprList(exprs=exprs))
        #funcCall.show()
        return funcCall


class FindFuncDef(c_ast.NodeVisitor):
    @beartype
    def __init__(self, funname:str)->None:
        self.funname
        self.result = None
    @beartype
    def visit_FuncDef(self, node:c_ast.Node) -> None:
        if node.decl.name == self.funname:
            assert self.result is None, self.result
            self.result = node
        
class ChangeVassumeVisitor(c_ast.NodeVisitor):
    @beartype
    def __init__(self, changeto:str) -> None:
        pass
            


# def show_func_calls(filename, funcname):
#     ast = parse_file(filename, use_cpp=True)
#     v = FuncCallVisitor(funcname)
#     v.visit(ast)



if __name__ == '__main__':
    parser = c_parser.CParser()
    ast = parser.parse(text)
    print(ast)
    
    fc = AddPrintfVisitor("vtrace")
    fc.visit(ast)
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
    generator = c_generator.CGenerator()
    print(generator.visit(ast))


    

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
