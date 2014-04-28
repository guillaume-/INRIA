open Ms_identifier;;
open Ms_syntax_tree;;
open SyntaxTree ;;

let str_id = Identifier.of_string
let rec str_id_list = function
	| [] -> "" 
	| e::[] -> (str_id e) 
	| e::q -> (str_id e) ^ ", " ^ (str_id_list q)
;;

let str_typed_variant_set (tv: typed_variant_set) =
	let rec str_typed_variant_list = function
		| []		-> ""
		| e::[]	-> (str_id e)
		| e::l	-> (str_id e)^", "^(str_typed_variant_list l)
	in match(IdentifierSet.elements tv.variant_set)with
		| [] -> "type "^(str_id tv.tv_type_name)^";\n"
		| l -> "type "^(str_id tv.tv_type_name)^" = enum ("^(str_typed_variant_list (IdentifierSet.elements tv.variant_set))^");\n"
;;

let str_direction = function
	| Input ->  "?"
	| Output -> "!"
	| Local -> "where"
;;

let rec str_signal_declaration  = function 
	| [] -> "" 
	| e::q ->  (str_id e.signal_type) ^ " " ^ (str_id e.signal_name) ^ ";\n" ^
		    (str_signal_declaration q)
;;

let rec str_sig_exp_l = function
	| [] -> ""
	| e::[] -> (str_signal_expression e) 
	| e::q -> (str_signal_expression e) ^ ", " ^ str_sig_exp_l q
and str_signal_expression =  function
	| EnumVariantAtom(i) -> str_id i
	| SignalAtom(i) -> str_id i
	| ClockPlus(e1, e2) -> (str_signal_expression e1) ^ " ^+ " ^ (str_signal_expression e2)
	| ClockMinus(e1, e2) -> (str_signal_expression e1) ^ " ^- " ^ (str_signal_expression e2)
	| ClockTimes(e1, e2) -> "(" ^ (str_signal_expression e1) ^ ") ^* (" ^ (str_signal_expression e2) ^ ")"
	| Delay(e1, e2) -> "(" ^ (str_signal_expression e1) ^ ") $1 init (" ^ (str_signal_expression e2) ^")"
	| EqualityAtom(e1, e2) -> "(" ^ (str_signal_expression e1) ^ ") = (" ^ (str_signal_expression e2) ^ ")"
	| InAtom(e, s)-> "(" ^ (str_signal_expression e) ^ ") in (" ^ (str_typed_variant_set s) ^ ")"
	| Default(e1, e2) -> "("^(str_signal_expression e1) ^ ") default (" ^ (str_signal_expression e2) ^")"
	| When(e1, e2) ->"(" ^ (str_signal_expression e1) ^ ") when (" ^ (str_signal_expression e2) ^ ")" 
	| WhenAtom(i)-> "when(" ^ (str_id i) ^")"
	| WhenNotAtom(i)-> "when not(" ^ (str_id i) ^")"
	| NotAtom(i)-> "not(" ^ (str_id i) ^ ")"
	| AndExp(e1, e2) ->"(" ^ (str_signal_expression e1) ^ ") and (" ^ (str_signal_expression e2) ^ ")"
	| OrExp(e1, e2)-> "(" ^(str_signal_expression e1) ^ ") or (" ^ (str_signal_expression e2) ^ ")"
	| IntegerConstant(i) -> (string_of_int i)
	| FunctionCall(i, sel)-> "call " ^ (str_id i) ^ "(" ^ (str_sig_exp_l sel) ^ ")"
	| Plus(e1,e2) ->   "(" ^(str_signal_expression e1) ^ ") + (" ^ (str_signal_expression e2) ^ ")"
	| Minus(e1,e2) ->   "(" ^(str_signal_expression e1) ^ ") - (" ^ (str_signal_expression e2) ^ ")"
	| Times(e1,e2) ->   "(" ^(str_signal_expression e1) ^ ") * (" ^ (str_signal_expression e2) ^ ")"
;;

let rec str_assignment = function
	|[] -> "" 
	| e::q -> "  | " ^ (str_id e.assigned_signal_name) ^ " := " ^ (str_signal_expression e.signal_expression)^ 
		"\n" ^ (str_assignment q)
;;

let str_sconstraint_kind = function
	| ClockEquality ->  " ^= "
	| ClockLeq  ->  " ^<= "
	| ClockLess ->  " ^< "
	| ClockWhen ->  " ^= when "
	| ClockWhenNot ->  " ^= when not "
	| ClockExclusive -> " ^# "
;;

let rec str_sconstraint = function
	| [] -> ""
	| sc::q -> "  | " ^ (str_id sc.left_signal_name) ^ " " ^
		    (str_sconstraint_kind sc.constraint_kind) ^ " " ^ 
		    (str_id sc.right_signal_name) ^ 
		    "\n" ^ str_sconstraint q
;;

let rec str_instantiation =  function
	| [] -> ""
	| e::q -> "  | submodule " ^ (str_id e.instance_process_name) ^ 
		  "(" ^ (str_id_list e.instance_output_signals) ^ ")" ^ 
		  "(" ^ (str_sig_exp_l e.instance_input_expressions) ^ ")" ^ 
		  "\n" ^
		  (str_instantiation q)
;;

let str_process_body b =
	"(\n" ^ (str_assignment b.assignment_list ) ^
	(str_sconstraint b.constraint_list) ^ 
	(str_instantiation b.instantiation_list) ^
	"|)\n"
;;

let str_signal_declarations d =
	let str_in_sig = if (List.length d.input_signal_list) > 0
			  then 
				(str_direction (List.hd d.input_signal_list).signal_direction) ^ " " ^
				(str_signal_declaration d.input_signal_list) 
			  else ""
    and str_out_sig = if (List.length d.output_signal_list) > 0
			  then 
				(str_direction (List.hd d.output_signal_list).signal_direction) ^ " " ^
				(str_signal_declaration d.output_signal_list) 
			  else ""
    in str_in_sig ^ str_out_sig
;;

let rec str_footer h =
    let str_pl = if (List.length h.local_process_list) > 0 
			then (str_process h.local_process_list) ^ "\n" 
			else ""
	in let d = h.signal_declarations
	in ((
		if (List.length d.local_signal_list) > 0 then 
			(str_direction (List.hd d.local_signal_list).signal_direction)^" "^(str_signal_declaration d.local_signal_list)
		else ""
	)^(str_pl)^"end;\n")
and str_process  =  function
	| [] -> "\n"
	| e::q -> (str_process_header e.header) ^ "\n" ^ 
		  (str_process_body e.body) ^ 
		  (str_footer e.header) ^ "\n" ^ 
		  (str_process q)
and str_process_header h = 
	"process " ^ (str_id h.process_name) ^ " = (\n" ^
	(str_signal_declarations h.signal_declarations) ^")" 
;;

let rec str_procedure_declaration  = function
	| [] ->  ""
	| e::q -> "procedure "  ^ 
		  (str_id e.procedure_name) ^ 
		  " (" ^ str_id_list e.procedure_input_list ^") -> " ^ (str_id e.procedure_output)^
		  ";\n" ^ 
		  (str_procedure_declaration q)
;;

let str_specification sp = 
	let rec str_t_v_s_l = function
		|[] -> ""
		| e::q -> (str_typed_variant_set e) ^ (str_t_v_s_l q)
	in 
		(str_t_v_s_l sp.type_declaration_list) ^ "\n" ^
		(str_procedure_declaration sp.procedure_declaration_list) ^ "\n" ^
		(str_process sp.process_list) 
;;
