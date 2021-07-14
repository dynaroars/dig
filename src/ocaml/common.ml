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

