import sys
import re
from pycparser import c_generator, c_ast, c_parser 
from helpers.vcommon import vwrite
from beartype import beartype
from pathlib import Path
import pdb
DBG = pdb.set_trace


def comment_remover(text):
    def replacer(match):
        s = match.group(0)
        if s.startswith('/'):
            return " " # note: a space and not an empty string
        else:
            return s
    pattern = re.compile(
        r'//.*?$|/\*.*?\*/|\'(?:\\.|[^\\\'])*\'|"(?:\\.|[^\\"])*"',
        re.DOTALL | re.MULTILINE
    )
    return re.sub(pattern, replacer, text)

class AddPrintfVisitor(c_ast.NodeVisitor):
    """
    add printf() calls to vtrace definitions
    """
    @beartype
    def __init__(self, vtrace: str) -> None:
        self.vtrace = vtrace

    @beartype
    def visit_FuncDef(self, node:c_ast.Node) -> None:
        if node.decl.name.startswith(self.vtrace) and not node.body.block_items:
            self._insert_funccall(node)

    @beartype
    def _insert_funccall(self,node:c_ast.FuncDef)-> None:
        myvars = [p.name for p in node.decl.type.args.params]
        funcalls  = self._create_new_funs(node.decl.name, myvars)
        node.body.block_items = funcalls



class AddPrintfCivl(AddPrintfVisitor):
    @beartype
    def _create_new_funs(self, myname: str, myvars: list[str]) -> list[c_ast.FuncCall]:
        value_ = "; ".join(f"{name} = %d" for name in myvars) + "\\n"
        myvars_ = [c_ast.ID(name=x) for x in myvars]
        exprs_ = [c_ast.Constant(type="string", 
                                 value=f'\"{myname}: {value_}"')] + myvars_
        funcCall = c_ast.FuncCall(name=c_ast.ID(name="printf"),
                                  args=c_ast.ExprList(exprs=exprs_))
        pc_call = c_ast.FuncCall(name=c_ast.ID(name="$pathCondition"), args=None)
        return [funcCall, pc_call]


class AddPrintfInstr(AddPrintfVisitor):
    @beartype
    def _create_new_funs(self, myname: str, myvars: list[str]) -> list[c_ast.FuncCall]:
        value = "; ".join("%d" for _ in myvars) + "\\n"
        myvars_ = [c_ast.ID(name=x) for x in myvars]
        exprs = [c_ast.Constant(type="string", 
                                value=f'\"{myname}; {value}"')] + myvars_
        funcCall = c_ast.FuncCall(name=c_ast.ID(name="printf"),
                                  args=c_ast.ExprList(exprs=exprs))
        return [funcCall]
    
class ChangeVassertVisitor(c_ast.NodeVisitor):
    # change vassert call to assert or $assert calls

    @beartype
    def __init__(self, fname:str, changeto:str) -> None:
        self.fname = fname
        self.changeto = changeto
        
    @beartype
    def visit_FuncCall(self, node:c_ast.Node) -> None:
        if node.name.name == self.fname:
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
        self.mainQ_params = []
        self.typ_info = []
        
    def visit_FuncDef(self, node:c_ast.Node) -> None:
        
        if node.decl.name.startswith(self.vtrace) or node.decl.name == self.mainQ:
            nts = [(p.name , p.type.type.names[0]) for p in node.decl.type.args.params]
            nts = '; '.join(("I " if t == "int" else "D ") + n for n,t in nts)
            self.typ_info.append(f"{node.decl.name}; {nts}")

        if node.decl.name == self.mainQ:
            self.mainQ_params = [(p.name , p.type.type.names[0])
                                 for p in node.decl.type.args.params]


class ChangeMainQCall(c_ast.NodeVisitor):
    """
    mainQ(atoi(argv[1], ...)  -> mainQ(x, ...)
    """
    def __init__(self, mainQ_params) -> None:
        self.mainQ_params = mainQ_params
        
    def visit_FuncDef(self, node:c_ast.Node) -> None:
        if node.decl.name == "main" and len(node.body.block_items) == 1:
            mainQ_names = [c_ast.ID(name=name) for name, _ in self.mainQ_params]
            funcCall = c_ast.FuncCall(name=c_ast.ID(name="mainQ"),
                                      args=c_ast.ExprList(exprs=mainQ_names))
            node.body.block_items = [funcCall]
    

@beartype
def gen(filename:Path, myast:c_ast.FileAST, includes:list[str]) -> None:
    generator = c_generator.CGenerator()
    instr = generator.visit(myast)
    instr = '\n'.join(includes + [instr])
    vwrite(filename, instr)

@beartype    
def instrument(filename:Path, tracefile:Path,  symexefile:Path) -> list[str]:
    includes = []
    src = []
    text = filename.read_text()
    text = comment_remover(text)
    
    for l in text.split('\n'):
        l = l.strip()
        if l.startswith("#include"):
            includes.append(l)
        else:
            src.append(l)

    if all(x for x in includes if "assert.h" not in x):
        includes.append("#include <assert.h>")

    src = '\n'.join(src)
    parser = c_parser.CParser()
    
    #trace instrumentation
    ast_instr = parser.parse(src)
    AddPrintfInstr("vtrace").visit(ast_instr)
    ChangeVassertVisitor("vassume", "assert").visit(ast_instr)
    gen(tracefile, ast_instr, includes)

    
    #civl instrumentation
    ast_civl =  parser.parse(src)
    #remove vassume def
    ast_civl.ext = [node for node in ast_civl.ext
                    if not (isinstance(node, c_ast.FuncDef) and
                            node.decl.name == "vassume")]
    # change vassume call to $assume
    ChangeVassertVisitor("vassume", "$assume").visit(ast_civl)
    # add printf and pathcond calls to vtrace defs
    AddPrintfCivl("vtrace").visit(ast_civl)
    vis = PrintTypeVisitor("vtrace", "mainQ")    
    vis.visit(ast_civl)
    
    #change mainQ(atoi(arg), ..) -> mainQ(x, ..)
    ChangeMainQCall(vis.mainQ_params).visit(ast_civl)
    includes = [i.replace('<','"').replace('>','"') for i in includes]
    inps = [f"$input {typ} {name};" for name, typ in vis.mainQ_params]
    gen(symexefile, ast_civl, ['#include "civlc.cvh"'] + includes + inps)
    return vis.typ_info


if __name__ == '__main__':
    filename = Path(sys.argv[1])
    symexefile = Path(sys.argv[2])    
    tracefile = Path(sys.argv[3])
    typ_output = instrument(filename, tracefile, symexefile)
    print('\n'.join(typ_info))
