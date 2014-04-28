open Ms_identifier
open Ms_syntax_tree
open SyntaxTree

(*****************************Type************************************************************)
let type_table =
	Hashtbl.create 1000

let gih_set_type (s: Identifier.t) (t:SyntaxTree.typed_variant_set) =
	Hashtbl.add type_table s t

let gih_get_type s = 
	try
		Hashtbl.find type_table s
	with
		Not_found -> failwith ("type id "^s^" not found")


(*****************************Procedure*******************************************************)
let procedure_table =
	Hashtbl.create 1000

let gih_get_procedure var = 
	try
		Hashtbl.find procedure_table var
	with
		Not_found -> failwith ("procedure "^var^" not found")

let gih_set_procedure (var:Identifier.t) (proc: SyntaxTree.procedure_declaration) = 
	Hashtbl.add procedure_table var proc


(*****************************Target**********************************************************)
type target =
    IH_enum_variant of SyntaxTree.typed_variant_set
  | IH_signal of SyntaxTree.signal_declaration
  | IH_ter
(* TER : code actuellement mort
  | IH_When of SyntaxTree.signal_declaration
  | IH_WhenNot of SyntaxTree.signal_declaration
  | IH_Not of SyntaxTree.signal_declaration
  | IH_Call of SyntaxTree.signal_declaration
*)

let target_table =
	Hashtbl.create 1000

let gih_get_target var = 
	try
		Hashtbl.find target_table var
	with
		Not_found -> IH_ter
      
let gih_set_target (var:Identifier.t) (tgt: target) = 
  Hashtbl.add target_table var tgt

let gih_set_signal var decl =
  gih_set_target var (IH_signal decl)

let gih_set_enum_variant var typ =
  gih_set_target var (IH_enum_variant typ)

(*****************************Process*********************************************************)
let process_table =
	Hashtbl.create 1000

let gih_get_process var =
	Hashtbl.find process_table var

let gih_set_process (var:Identifier.t) (proc: SyntaxTree.process) = 
	Hashtbl.add process_table var proc
