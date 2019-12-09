open Cil
module E = Errormsg
module H = Hashtbl
module P = Printf	     
module L = List
module S = String
module CM = Common	     

let is_vtrace vname vtrace =
      let vtrace_len = S.length vtrace in   
      S.length vname >= vtrace_len &&
           S.sub vname 0 vtrace_len = vtrace
      
class add_printf_visitor vtrace = object(self)
  inherit nopCilVisitor

  method private create_printf_stmt fd : stmt =
    (*Create printf statement, e.g., printf("%d %d %g", x, y, z)*)
    let s = L.map (
                fun vi -> if vi.vtype = intType then "%d" else "%g"
              ) fd.sformals in
                
    let s = fd.svar.vname ^ ": " ^ S.concat " " s  ^ "\n" in
    let myprintf:instr = CM.mkCall "printf"
                         (Const (CStr(s))::(L.map CM.exp_of_vi fd.sformals)) in
    mkStmt (Instr([myprintf]))

  method vfunc f =
    let action f:fundec =
      if is_vtrace f.svar.vname vtrace then (
        f.sbody.bstmts <- [self#create_printf_stmt f] @ f.sbody.bstmts
      );
      f in 
    ChangeDoChildrenPost(f, action)
end



(*CVIL instrumentation*)
class add_symstates_visitor vtrace = object(self)
  inherit nopCilVisitor

  method private create_printf_stmt fd : stmt =
    (*Create printf statement, e.g., printf("%d %d %g", x, y, z)*)
    let s = L.map (fun vi ->
                vi.vname ^ " = " ^ if vi.vtype = intType then "%d" else "%g"
              ) fd.sformals in
                
    let s = fd.svar.vname ^ ": " ^ S.concat "; " s  ^ "\n" in
    let myprintf:instr = CM.mkCall "printf"
                         (Const (CStr(s))::(L.map CM.exp_of_vi fd.sformals)) in
    mkStmtOneInstr myprintf

  method private create_print_pathcondition : stmt =
    let myinstr:instr = CM.mkCall "$pathCondition" [] in
    mkStmtOneInstr myinstr
    
  method vfunc f =
    let action f:fundec =
      if is_vtrace f.svar.vname vtrace then (
        f.sbody.bstmts <- [self#create_printf_stmt f; self#create_print_pathcondition] @ f.sbody.bstmts
      );
      f in 
    ChangeDoChildrenPost(f, action)
end


let create_call_mainQ mainQ_fd =
  let inps = L.map (fun vi -> CM.expOfVi vi) mainQ_fd.sformals in 
  mkStmtOneInstr (CM.mkCall mainQ_fd.svar.vname inps)
                                
let create_inps (vars:varinfo list): string list =
  (** create 
      $input int x;
      $input int y;
      let typ = if vi.vtype = intType then "int"
      else E.s(E.error "not supporting type %a" d_type vi.vtype)

   **)                                
  L.map (fun vi ->
      "$input " ^ "int"  ^ " " ^ vi.vname ^ ";"
    ) vars
                       

class change_vassume_visitor vassume changeto = object
  (*
    change vassume(..) to $assume(..)
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
  
  
let () = begin
    
    initCIL();
    Cil.lineDirectiveStyle:= None; (*reduce code, remove all junk stuff*)
    Cprint.printLn := false; (*don't print line #*)
    (* for Cil to retain &&, ||, ?: instead of transforming them to If stmts *)
    Cil.useLogicalOperators := true;

    let src = Sys.argv.(1) in
    let civl_src = Sys.argv.(2) in   (*instrument for CIVL*)
    let trace_src = civl_src ^ ".trace.c"  in (*instrument for execution*)
    let cil_src = civl_src ^ ".cil.c"  in (*instrument for execution*)

    let ast_civl = Frontc.parse src () in    
    CM.writeSrc cil_src ast_civl;

    let mainQ = "mainQ" in
    let vtrace = "vtrace" in 
    let vassume = "vassume" in     
    
    let myglobals:global list = foldGlobals ast_civl (fun l g ->
                        match g with 
                        |GFun(f, _) when f.svar.vname = vassume -> l
                        |x -> x::l
                      ) [] in 
    let myglobals = L.rev myglobals in 
    ast_civl.globals <- myglobals;
    let ast_trace = CM.copyObj ast_civl in    
    
    (* CIVL Instrumentation *)
    
    let mainQ_fd:fundec = CM.find_fun ast_civl mainQ in
    visitCilFileSameGlobals (new add_symstates_visitor vtrace) ast_civl;
    ignore(visitCilFunction (new change_vassume_visitor vassume "$assume")
             mainQ_fd);
    let includes = ["civlc.cvh"; "stdio.h"] in 
    let includes = L.map(fun x -> "#include \"" ^ x ^ "\"") includes in
    let inps:string list = create_inps mainQ_fd.sformals in
    let adds = includes @ inps in
    let adds = S.concat "\n" adds in
    ast_civl.globals <- (GText adds):: ast_civl.globals;
    
    
    let main_fd:fundec = CM.find_fun ast_civl "main" in
    main_fd.sbody <- mkBlock [create_call_mainQ mainQ_fd];
    main_fd.slocals <- [];
    CM.writeSrc civl_src ast_civl;
    

    (* Trace/Execution Instrumentation *)
    visitCilFileSameGlobals (new add_printf_visitor "vtrace") ast_trace;
    let mainQ_fd:fundec = CM.find_fun ast_trace mainQ in    
    ignore(visitCilFunction (new change_vassume_visitor vassume "assert") mainQ_fd);
    
    let includes = ["stdio.h"; "stdlib.h"] in 
    let includes = L.map(fun x -> "#include \"" ^ x ^ "\"") includes in
    let adds = S.concat "\n" includes in
    ast_trace.globals <- (GText adds):: ast_trace.globals;
    
    CM.writeSrc trace_src ast_trace

end



    (* visitCilFileSameGlobals (new CM.everyVisitor) ast;
     * visitCilFileSameGlobals (new CM.breakCondVisitor :> cilVisitor) ast;
     * 
     * let correctQ_fd:fundec = CM.findFun ast correctQ_name in    
     * 
     * let ignoreFuns:CM.SS.t =
     *   L.fold_right CM.SS.add ["main" ; mainQ_name; correctQ_name] CM.SS.empty in
     * 
     * (\*add stmt id*\)
     * let stmtHt = H.create 1024 in
     * visitCilFileSameGlobals (new CM.numVisitor stmtHt ignoreFuns :> cilVisitor) ast;
     * 
     * CM.write_file_bin ast_file (ast, main_fd, mainQ_fd, correctQ_fd, stmtHt) *)

           



(* let stderrVi = CM.mkVi ~ftype:(TPtr(TVoid [], [])) "_coverage_fout"*)
(*
  walks over AST and preceeds each stmt with a printf that writes out its sid
  create a stmt consisting of 2 Call instructions
  fprintf "_coverage_fout, sid"; 
  fflush();
 *)
      
(* class coverageVisitor = object(self)
 *   inherit nopCilVisitor
 * 
 *   method private create_fprintf_stmt (sid : CM.sid_t) :stmt = 
 *   let str = P.sprintf "%d\n" sid in
 *   let stderr = CM.expOfVi stderrVi in
 *   let instr1 = CM.mkCall "fprintf" [stderr; Const (CStr(str))] in 
 *   let instr2 = CM.mkCall "fflush" [stderr] in
 *   mkStmt (Instr([instr1; instr2]))
 *     
 *   method vblock b = 
 *     let action (b: block) :block= 
 *       let insert_printf (s: stmt): stmt list = 
 * 	if s.sid > 0 then [self#create_fprintf_stmt s.sid; s]
 * 	else [s]
 *       in
 *       let stmts = L.map insert_printf b.bstmts in 
 *       {b with bstmts = L.flatten stmts}
 *     in
 *     ChangeDoChildrenPost(b, action)
 *       
 *   method vfunc f = 
 *     let action (f: fundec) :fundec = 
 *       (\*print 0 when entering main so we know it's a new run*\)
 *       if f.svar.vname = "main" then (
 * 	f.sbody.bstmts <- [self#create_fprintf_stmt 0] @ f.sbody.bstmts
 *       );
 *       f
 *     in
 *     ChangeDoChildrenPost(f, action)
 * end *)


(* let spy_mainQ mainQ_fd =
 *   (\*let mainQ_typ:typ = match mainQ_fd.svar.vtype in*\)
 *   L.map (fun vi ->
 *       P.printf "%s %s\n" (CM.string_of_typ vi.vtype) vi.vname
 *     ) mainQ_fd.sformals ;
 *   () *)
           
