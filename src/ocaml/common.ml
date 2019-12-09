open Cil
module E = Errormsg
module H = Hashtbl
module P = Printf
module L = List

module SS = Set.Make(String)

let string_of_typ (s:typ) = Pretty.sprint ~width:80 (dn_type () s)
let string_of_stmt (s:stmt) = Pretty.sprint ~width:80 (dn_stmt () s) 
let string_of_exp (s:exp) = Pretty.sprint ~width:80 (dn_exp () s) 
let string_of_instr (s:instr) = Pretty.sprint ~width:80 (dn_instr () s) 
let string_of_lv (s:lval) = Pretty.sprint ~width:80 (dn_lval () s)

let const_exp_of_string (t:typ) (s:string): exp = match t with
  |TInt _ -> integer (int_of_string s)
  |TFloat(fk,_) -> Const(CReal(float_of_string s,fk,None))
  |_-> E.s(E.error "unexp typ %a " dn_type t)

	  
let string_of_list ?(delim:string = ", ") =  String.concat delim
let str_split s:string list =  Str.split (Str.regexp "[ \t]+") s
							   
let rec range ?(a=0) b = if a >= b then [] else a::range ~a:(succ a) b

(*check if s1 is a substring of s2*)
let in_str s1 s2 = 
  try ignore (Str.search_forward (Str.regexp_string s1) s2 0); true
  with Not_found -> false
		      
let copyObj (x : 'a) = 
  let s = Marshal.to_string x [] in (Marshal.from_string s 0 : 'a)
				      
let writeSrc ?(use_stdout:bool=false)
    (filename:string) (ast:file): unit = 
  let df oc =  dumpFile defaultCilPrinter oc filename ast in
  if use_stdout then df stdout else (
    let fout = open_out filename in
    df fout;
    close_out fout;
    P.printf "write: %s\n" filename
  )

let write_file_bin (filename:string) content: unit = 
  let fout = open_out_bin filename in
  Marshal.to_channel fout content [];
  close_out fout;
  P.printf "write_file_bin: '%s'\n%!" filename

let read_file_bin (filename:string) =
  let fin = open_in_bin filename in
  let content = Marshal.from_channel fin in
  close_in fin;
  P.printf "read_file: '%s'\n%!" filename;
  content

let read_file_ascii ?(keep_empty=true) (filename:string) :string list =
  let lines:string list ref = ref [] in
  let fin = open_in filename in
  (try
     while true do 
       let line = String.trim (input_line fin) in 
       lines := line::!lines
       done
   with _ -> close_in fin);

  let lines = L.rev !lines in 
  if keep_empty then lines else L.filter (fun l -> l <> "") lines    
				      
(* Visitors *)

(** Stmts that can be tracked for fault loc and modified for bug fix **)
let canModify : stmtkind -> bool = function 
  |Instr[Set(_)] -> true
  |_ -> false

let canConsider (funName:string) (ignoreFuns:SS.t): bool =
    (* let printSet s = SS.iter print_endline s in *)
    (* printSet ignoreFuns; *)
  
  let rv =  not (SS.exists (fun iFun -> in_str iFun funName) ignoreFuns) in 
  (*if rv then P.printf "can consider fun %s\n" funName else P.printf "NOT consider fun %s\n" funName;*)
  rv


class numVisitor ht (ignoreFuns:SS.t) = object(self)
  inherit nopCilVisitor

  val mutable mctr = 1
  val mutable curFd = None

  method vfunc f =
    (*P.printf "function %s\n" f.svar.vname;*)
    curFd <- (Some f); DoChildren

  method vblock b = 
    let action (b: block) : block= 
      let change_sid (s: stmt) : unit =
	if canModify s.skind then (
	  match curFd with 
	  | Some f -> (
	    if canConsider f.svar.vname ignoreFuns then (
		s.sid <- mctr;
		H.add ht mctr (s, f);
		mctr <- succ mctr
	    )
	  )
	  | None -> E.s(E.error "not in a function")
	)
	else s.sid <- 0;  (*Anything not considered has sid 0 *)
      in 
      L.iter change_sid b.bstmts; 
      b
    in 
    ChangeDoChildrenPost(b, action)

end
			 
(*Makes every instruction into its own stmt*)
class everyVisitor = object
  inherit nopCilVisitor
  method vblock b = 
    let action (b: block) : block = 
      let change_stmt (s: stmt) : stmt list = 
	match s.skind with
	|Instr(h::t) -> {s with skind = Instr([h])}::L.map mkStmtOneInstr t
	|_ -> [s]
      in
      let stmts = L.flatten (L.map change_stmt b.bstmts) in
      {b with bstmts = stmts}
    in
    ChangeDoChildrenPost(b, action)
end
				      


class breakCondVisitor = object(self)
  inherit nopCilVisitor
  val mutable curFd = None
  method vfunc f = curFd <- (Some f); DoChildren

  method private mk_stmt s e loc: lval*stmt= 
    let fd = match curFd with 
      | Some f -> f | None -> E.s(E.error "not in a function") in
    let v:lval = var(makeTempVar fd (typeOf e)) in
    let i:instr = Set(v,e,loc) in
    v, {s with skind = Instr[i]} 

  method vblock b = 
    let action (b: block) : block = 

      let rec change_stmt (s: stmt) : stmt list = 
	match s.skind with
	(*if (e){b1;}{b2;} ->  int t = e; if (t){b1;}{b2;} *)
	|If(e,b1,b2,loc) -> 
	  let v, s1 = self#mk_stmt s e loc in
	  let s1s = change_stmt s1 in
	  let s2 = mkStmt (If (Lval v,b1,b2,loc)) in
	  let rs = s1s@[s2] in
	    (* if !vdebug then E.log "(If) break %a\n ton%s\n"  *)
	    (*   dn_stmt s (String.concat "\n" (L.map string_of_stmt rs)); *)
	  
	  rs
	    
	(*return e; ->  int t = e; return t;*)
	|Return(Some e,loc) ->
	  let v, s1 = self#mk_stmt s e loc in
	  let s1s = change_stmt s1 in
	  
	  let s2 = mkStmt (Return (Some (Lval v), loc)) in
	  let rs =  s1s@[s2] in
		  (* if !vdebug then E.log "(Return) break %a\nto\n%s\n"  *)
		  (*   dn_stmt s (String.concat "\n" (L.map string_of_stmt rs)); *)
	  
	  rs
	    
	(*x = a?b:c  -> if(a){x=b}{x=c} *)
	|Instr[Set(lv,Question (e1,e2,e3,ty),loc)] ->
	  let i1,i2 = Set(lv,e2,loc), Set(lv,e3,loc) in
	  let sk = If(e1,
		      mkBlock [mkStmtOneInstr i1],
		      mkBlock [mkStmtOneInstr i2], 
		      loc) in
	  let s' = mkStmt sk in
	  let rs = change_stmt s' in 
	  rs
	    
	|_ -> [s]
      in
      let stmts = L.flatten (L.map change_stmt b.bstmts) in
      {b with bstmts = stmts}
    in
    ChangeDoChildrenPost(b, action)
end

let boolTyp:typ = intType
type sid_t = int
let mkVi ?(ftype=TVoid []) fname: varinfo = makeVarinfo true fname ftype
let expOfVi (vi:varinfo): exp = Lval (var vi)
let mkCall ?(ftype=TVoid []) ?(av=None) (fname:string) args : instr = 
  let f = var(mkVi ~ftype:ftype fname) in
  Call(av, Lval f, args, !currentLoc)
			   
let find_fun (ast:file) (fun_name:string) : fundec = 
  let fd = ref None in
  iterGlobals ast (function 
      | GFun(f,_) when f.svar.vname = fun_name -> fd := Some f
      | _ -> ()
		  );
  match !fd with
  |Some f -> f
  |None -> E.s(E.error "fun '%s' not in '%s'!" fun_name ast.fileName)


let exp_of_vi (vi:varinfo): exp = Lval (var vi)
				       
(*[Some 1, None, Some 2] -> [1,2]*)
let list_of_some (l:'a option list):'a list = 
  let rs = 
    L.fold_left (fun l' -> function |Some f -> f::l' |None -> l') [] l
  in L.rev rs


(*Instrument common*)
let mkUk
      (uid:int) (utyp:typ)
      (minV:int)
      (maxV:int)
      (mainFd: fundec)
    :(varinfo*instr list) =
  
  let vname = "uk_" ^ string_of_int uid in
  let vi:varinfo = makeLocalVar mainFd vname utyp in
  let lv:lval = var vi in
  
  (*klee_make_symbolic(&uk,sizeof(uk),"uk")*)
  let mkSymInstr:instr =
    mkCall "klee_make_symbolic"
	   [mkAddrOf(lv); SizeOfE(Lval lv); Const (CStr vname)]
  in
  let maxE = integer maxV in
  let minE = integer minV  in
  let klee_assert_lb:instr =
    mkCall "klee_assume" [BinOp(Le, minE, Lval lv, boolTyp)] in
  
  let klee_assert_ub:instr =
    mkCall "klee_assume" [BinOp(Le, Lval lv, maxE, boolTyp)] in
  	      
  (vi, [mkSymInstr; klee_assert_lb; klee_assert_ub])
	   
    
