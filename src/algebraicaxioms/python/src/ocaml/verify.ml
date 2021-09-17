open Cil
module E = Errormsg
module H = Hashtbl
module P = Printf
module L = List
module S = String
module CM = Common

let modify_vtrace (vtrace:fundec) (inv:string) =
  let error:instr = CM.mkCall "__VERIFIER_error" [] in
  let ifblock:stmtkind = If(Const (CStr inv), mkBlock [], mkBlock ([mkStmtOneInstr error]), !currentLoc) in
  vtrace.sbody.bstmts <- mkStmt ifblock :: vtrace.sbody.bstmts

class change_vassume_visitor vassume changeto = object
  (*
    change vassume(..) to __VERIFIER_assume(..)
   *)
  inherit nopCilVisitor

  method vinst i =
    match i with
    | Call(lvopt, (Lval(Var(vi),NoOffset)), args,loc)
         when vi.vname = vassume ->
       let i' = CM.mkCall changeto args in
       ChangeTo([i'])
    | _ -> SkipChildren
end

let mkMain mainFd mainQ_fd =
  let tmp_vars = L.map (fun vi -> makeTempVar mainFd vi.vtype) mainQ_fd.sformals in
  let tmp_instr = L.map (fun vi -> CM.mkCall ~ftype:    (*CM.writeSrc cil_src ast_trace;*)
vi.vtype ~av:(Some (var vi)) "__VERIFIER_nondet_int" []) tmp_vars in

  let inps = L.map (fun vi -> CM.expOfVi vi) tmp_vars in
  let icall = CM.mkCall mainQ_fd.svar.vname inps in
  let stmt2:stmtkind = Instr(tmp_instr @ [icall]) in

  let stmts = [mkStmt stmt2] in
  mainFd.sbody.bstmts <- stmts

let () = begin

    initCIL();
    Cil.lineDirectiveStyle:= None; (*reduce code, remove all junk stuff*)
    Cprint.printLn := false; (*don't print line #*)
    (* for Cil to retain &&, ||, ?: instead of transforming them to If stmts *)
    Cil.useLogicalOperators := true;

    let src = Sys.argv.(1) in
    let trace_src = Sys.argv.(2) in   (*instrument for CIVL*)
    let loc = Sys.argv.(3) in (* enter 0 if only one vtrace function*)
    let inv = Sys.argv.(4) in

    let ast_trace = Frontc.parse src () in

    let mainQ = "mainQ" in
    let vassume = "vassume" in

    let myglobals:global list = foldGlobals ast_trace (fun l g ->
                        match g with
                        |GFun(f, _) when f.svar.vname = vassume -> l
                        |x -> x::l
                      ) [] in
    let myglobals = L.rev myglobals in
    ast_trace.globals <- myglobals;

    let mainQ_fd:fundec = CM.find_fun ast_trace mainQ in
    let mainFd:fundec = CM.find_fun ast_trace "main" in
    let vtraceFd:fundec =
    if (int_of_string loc)==0 then CM.find_fun ast_trace "vtrace"
    else CM.find_fun ast_trace ("vtrace" ^ loc) in

    modify_vtrace vtraceFd inv;

    mkMain mainFd mainQ_fd;
    ignore(visitCilFunction (new change_vassume_visitor vassume "__VERIFIER_assume") mainQ_fd);

    let includes = ["<stdio.h>"; "<stdlib.h>"] in
    let includes = L.map(fun x -> "#include \"" ^ x ^ "\"") includes in
    let adds = S.concat "\n" includes in
    ast_trace.globals <- (GText adds):: ast_trace.globals;

    CM.writeSrc trace_src ast_trace;

    let file = CM.read_file_ascii trace_src in
    let oc = open_out trace_src in
    ignore(L.map(fun s ->
        let newstring = Str.replace_first (Str.regexp_string "\"") "(" s in
        P.fprintf oc "%s\n" (Str.replace_first (Str.regexp_string "\"") ")" newstring)) file);
    close_out oc


end
